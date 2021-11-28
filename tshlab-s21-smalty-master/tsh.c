/**
 * @file tsh.c
 * @brief A tiny shell program with job control
 *
 * TODO: Delete this comment and replace it with your own.
 * <The line above is not a sufficient documentation.
 *  You will need to write your program documentation.
 *  Follow the 15-213/18-213/15-513 style guide at
 *  http://www.cs.cmu.edu/~213/codeStyle.html.>
 *
 * @author Edric Eun <eeun@andrew.cmu.edu>
 */

#include "csapp.h"
#include "tsh_helper.h"

#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

/*
 * If DEBUG is defined, enable contracts and printing on dbg_printf.
 */
#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Function prototypes */
void eval(const char *cmdline);

void sigchld_handler(int sig);
void sigtstp_handler(int sig);
void sigint_handler(int sig);
void sigquit_handler(int sig);
void cleanup(void);

/**
 * @brief <Write main's function header documentation. What does main do?>
 *
 * TODO: Delete this comment and replace it with your own.
 *
 * "Each function should be prefaced with a comment describing the purpose
 *  of the function (in a sentence or two), the function's arguments and
 *  return value, any error cases that are relevant to the caller,
 *  any pertinent side effects, and any assumptions that the function makes."
 */
int main(int argc, char **argv) {
    int c;
    char cmdline[MAXLINE_TSH]; // Cmdline for fgets
    bool emit_prompt = true;   // Emit prompt (default)

    // Redirect stderr to stdout (so that driver will get all output
    // on the pipe connected to stdout)
    if (dup2(STDOUT_FILENO, STDERR_FILENO) < 0) {
        perror("dup2 error");
        exit(1);
    }

    // Parse the command line
    while ((c = getopt(argc, argv, "hvp")) != -1) {
        switch (c) {
        case 'h': // Prints help message
            usage();
            break;
        case 'v': // Emits additional diagnostic info
            verbose = true;
            break;
        case 'p': // Disables prompt printing
            emit_prompt = false;
            break;
        default:
            usage();
        }
    }

    // Create environment variable
    if (putenv("MY_ENV=42") < 0) {
        perror("putenv error");
        exit(1);
    }

    // Set buffering mode of stdout to line buffering.
    // This prevents lines from being printed in the wrong order.
    if (setvbuf(stdout, NULL, _IOLBF, 0) < 0) {
        perror("setvbuf error");
        exit(1);
    }

    // Initialize the job list
    init_job_list();

    // Register a function to clean up the job list on program termination.
    // The function may not run in the case of abnormal termination (e.g. when
    // using exit or terminating due to a signal handler), so in those cases,
    // we trust that the OS will clean up any remaining resources.
    if (atexit(cleanup) < 0) {
        perror("atexit error");
        exit(1);
    }

    // Install the signal handlers
    Signal(SIGINT, sigint_handler);   // Handles Ctrl-C
    Signal(SIGTSTP, sigtstp_handler); // Handles Ctrl-Z
    Signal(SIGCHLD, sigchld_handler); // Handles terminated or stopped child

    Signal(SIGTTIN, SIG_IGN);
    Signal(SIGTTOU, SIG_IGN);

    Signal(SIGQUIT, sigquit_handler);

    // Execute the shell's read/eval loop
    while (true) {
        if (emit_prompt) {
            printf("%s", prompt);

            // We must flush stdout since we are not printing a full line.
            fflush(stdout);
        }

        if ((fgets(cmdline, MAXLINE_TSH, stdin) == NULL) && ferror(stdin)) {
            perror("fgets error");
            exit(1);
        }

        if (feof(stdin)) {
            // End of file (Ctrl-D)
            printf("\n");
            return 0;
        }

        // Remove any trailing newline
        char *newline = strchr(cmdline, '\n');
        if (newline != NULL) {
            *newline = '\0';
        }

        // Evaluate the command line
        eval(cmdline);
    }

    return -1; // control never reaches here
}

/**
 * @brief Eval evaluates the cmd line and runs it in the shell
 *
 * The eval will parse the line and send jobs in either the background
 * or foreground, updating the joblist along the way.
 *
 * NOTE: The shell is supposed to be a long-running process, so this function
 *       (and its helpers) should avoid exiting on error.  This is not to say
 *       they shouldn't detect and print (or otherwise handle) errors!
 */
void eval(const char *cmdline) {
    parseline_return parse_result;
    struct cmdline_tokens token;
    sigset_t mask;
    sigset_t prev_mask;
    sigaddset(&mask, SIGCHLD);
    sigaddset(&mask, SIGINT);
    sigaddset(&mask, SIGTSTP);
    // Parse command line
    parse_result = parseline(cmdline, &token);
    // If parse goes wrong, go to next line
    if (parse_result == PARSELINE_ERROR || parse_result == PARSELINE_EMPTY) {
        return;
    }
    // Exit on quit line
    if (token.builtin == BUILTIN_QUIT) {
        exit(0);
    }
    // List jobs built in
    if (token.builtin == BUILTIN_JOBS) {
        sigprocmask(SIG_BLOCK, &mask, &prev_mask);
        if (token.outfile == NULL) {
            if (!list_jobs(STDOUT_FILENO)) {
                sio_printf("Error writing list to file descriptor\n");
            }
        } else {
            int fd;
            if ((fd = open(token.outfile, O_WRONLY | O_CREAT | O_TRUNC,
                           DEF_MODE)) < 0) {
                perror(token.outfile);
            } else if (!list_jobs(fd)) {
                sio_printf("Error writing list to file descriptor\n");
            }
            close(fd);
        }
        sigprocmask(SIG_SETMASK, &prev_mask, NULL);
        return;
    }
    /* Send specified job or pid (given by second argument) to work in
     * background. Gives appropriate error messages if input is incorrect
     * or job does not exist.
     */
    if (token.builtin == BUILTIN_BG) {
        sigprocmask(SIG_BLOCK, &mask, &prev_mask);
        jid_t jid;
        pid_t pid;
        // If there is no second argument
        if (token.argc == 1) {
            sio_printf("bg command requires PID or %%jobid argument\n");
            sigprocmask(SIG_SETMASK, &prev_mask, NULL);
            return;
        }
        // If the second argument starts with %
        if ((token.argv[1])[0] == '%') {
            int jid_int;
            // If the second argument is not a jid
            if (sscanf(token.argv[1], "%%%d", &jid_int) != 1) {
                sio_printf("bg:argument must be a PID or %%jobid\n");
                sigprocmask(SIG_SETMASK, &prev_mask, NULL);
                return;
            } else {
                jid = (jid_t)(jid_int);
                // If the job does not exist
                if (!job_exists(jid)) {
                    sio_printf("%%%d: No such job\n", jid);
                    sigprocmask(SIG_SETMASK, &prev_mask, NULL);
                    return;
                }
            }
        } else {
            // If the second argument does not start with %
            int pid_int;
            // If the second argument is not an integer
            if (sscanf(token.argv[1], "%d", &pid_int) != 1) {
                sio_printf("bg:argument must be a PID or %%jobid\n");
                sigprocmask(SIG_SETMASK, &prev_mask, NULL);
                return;
            }
            pid = (pid_t)(pid_int);
            jid = job_from_pid(pid);
        }
        if (job_exists(jid)) {
            job_set_state(jid, BG);
            pid = job_get_pid(jid);
            // Send the job the SIGCONT signal
            kill(-pid, SIGCONT);
            sio_printf("[%d] (%d) %s\n", jid, pid, job_get_cmdline(jid));
        }
        sigprocmask(SIG_SETMASK, &prev_mask, NULL);
        return;
    }
    /* Send specified job or pid (given by second argument) to work in
     * foreground. Gives appropriate error messages if input is incorrect
     * or job does not exist.
     */
    if (token.builtin == BUILTIN_FG) {
        sigprocmask(SIG_BLOCK, &mask, &prev_mask);
        jid_t jid;
        pid_t pid;
        // If there is no second argument
        if (token.argc == 1) {
            sio_printf("fg command requires PID or %%jobid argument\n");
            sigprocmask(SIG_SETMASK, &prev_mask, NULL);
            return;
        }
        // If second argument starts with %
        if ((token.argv[1])[0] == '%') {
            int jid_int;
            // If second argument is not jid
            if (sscanf(token.argv[1], "%%%d", &jid_int) != 1) {
                sio_printf("fg:argument must be a PID or %%jobid\n");
                sigprocmask(SIG_SETMASK, &prev_mask, NULL);
                return;
            } else {
                jid = (jid_t)(jid_int);
                // If jid does not exist
                if (!job_exists(jid)) {
                    sio_printf("%%%d: No such job\n", jid);
                    sigprocmask(SIG_SETMASK, &prev_mask, NULL);
                    return;
                }
            }
        } else {
            // If second argument does not start with %
            int pid_int;
            // If second argument is not an integer
            if (sscanf(token.argv[1], "%d", &pid_int) != 1) {
                sio_printf("fg:argument must be a PID or %%jobid\n");
                sigprocmask(SIG_SETMASK, &prev_mask, NULL);
                return;
            }
            pid = (pid_t)(pid_int);
            jid = job_from_pid(pid);
        }
        if (job_exists(jid)) {
            job_set_state(jid, FG);
            pid = job_get_pid(jid);
            // Send the job the SIGCONT signal
            kill(-pid, SIGCONT);
            // Suspend foreground job
            while (fg_job() > 0) {
                sigsuspend(&prev_mask);
            }
        }
        sigprocmask(SIG_SETMASK, &prev_mask, NULL);
        return;
    }
    /* Runs the program specified by cmd line in either the background or
     * foreground given parse_result
     */
    if (token.builtin == BUILTIN_NONE) {
        sigprocmask(SIG_BLOCK, &mask, &prev_mask);
        pid_t pid = fork();
        if (pid == 0) {
            setpgid(0, 0);
            // If token.infile is not null, set up fd to STDIN_FILENO
            if (token.infile != NULL) {
                int fd;
                if ((fd = open(token.infile, O_RDONLY, DEF_MODE)) < 0) {
                    perror(token.infile);
                    fflush(0);
                    _exit(1);
                } else {
                    dup2(fd, STDIN_FILENO);
                }
                close(fd);
            }
            // If token.outfile is not null, set up fd to STDOUT_FILENO
            if (token.outfile != NULL) {
                int fd;
                if ((fd = open(token.outfile, O_WRONLY | O_CREAT | O_TRUNC,
                               DEF_MODE)) < 0) {
                    perror(token.outfile);
                    fflush(0);
                    _exit(1);
                } else {
                    dup2(fd, STDOUT_FILENO);
                }
                close(fd);
            }
            sigprocmask(SIG_SETMASK, &prev_mask, NULL);
            if (execve(token.argv[0], token.argv, environ) < 0) {
                perror(token.argv[0]);
                exit(1);
            }
        }
        // Suspend if job is in foreground
        if (parse_result == PARSELINE_FG) {
            add_job(pid, FG, cmdline);
            while (fg_job() > 0) {
                sigsuspend(&prev_mask);
            }
            sigprocmask(SIG_SETMASK, &prev_mask, NULL);
        }
        // Print if job is in background
        if (parse_result == PARSELINE_BG) {
            jid_t jid = add_job(pid, BG, cmdline);
            sio_printf("[%d] (%d) %s\n", jid, pid, cmdline);
            sigprocmask(SIG_SETMASK, &prev_mask, NULL);
        }
    }
    return;
}

/*****************
 * Signal handlers
 *****************/

/**
 * @brief Handle sigchild signal which is sent when child prcess
 * is done, stopped, or terminated. The handler will reap all processes
 * that are available to be reaped, and delete the jobs that are done
 * or terminated.
 *
 */
void sigchld_handler(int sig) {
    pid_t pid;
    int status;
    int err = errno;
    sigset_t mask;
    sigset_t prev_mask;
    sigfillset(&mask);
    sigprocmask(SIG_BLOCK, &mask, &prev_mask);
    while ((pid = waitpid(-1, &status, WNOHANG | WUNTRACED)) > 0) {
        jid_t jid = job_from_pid(pid);
        // Case child is stopped
        if (WIFSTOPPED(status)) {
            job_set_state(jid, ST);
            sio_printf("Job [%d] (%d) stopped by signal %d\n", jid, pid,
                       WSTOPSIG(status));
        }
        // Case child is terminated
        if (WIFSIGNALED(status)) {
            sio_printf("Job [%d] (%d) terminated by signal %d\n", jid, pid,
                       WTERMSIG(status));
        }
        // Delete job if job state is not ST
        if (job_get_state(jid) == FG || job_get_state(jid) == BG) {
            if (!delete_job(jid)) {
                sio_printf("No job with job id exists in job list\n");
            }
        }
    }
    sigprocmask(SIG_SETMASK, &prev_mask, NULL);

    errno = err;
    return;
}

/**
 * @brief The sigint_handler will send the SIGINT signal
 * to the current forground job if the job exists.
 *
 */
void sigint_handler(int sig) {
    jid_t jid;
    int err = errno;
    sigset_t mask;
    sigset_t prev_mask;
    sigfillset(&mask);
    sigprocmask(SIG_BLOCK, &mask, &prev_mask);
    jid = fg_job();
    if (job_exists(jid)) {
        pid_t pid = job_get_pid(jid);
        kill(-pid, SIGINT);
    }
    sigprocmask(SIG_SETMASK, &prev_mask, NULL);
    errno = err;
    return;
}

/**
 * @brief The sigint_handler will send the SIGTSTP signal
 * to the current forground job if the job exists.
 *
 */
void sigtstp_handler(int sig) {
    jid_t jid;
    int err = errno;
    sigset_t mask;
    sigset_t prev_mask;
    sigfillset(&mask);
    sigprocmask(SIG_BLOCK, &mask, &prev_mask);
    jid = fg_job();
    if (job_exists(jid)) {
        pid_t pid = job_get_pid(jid);
        kill(-pid, SIGTSTP);
    }
    sigprocmask(SIG_SETMASK, &prev_mask, NULL);
    errno = err;
    return;
}

/**
 * @brief Attempt to clean up global resources when the program exits.
 *
 * In particular, the job list must be freed at this time, since it may
 * contain leftover buffers from existing or even deleted jobs.
 */
void cleanup(void) {
    // Signals handlers need to be removed before destroying the joblist
    Signal(SIGINT, SIG_DFL);  // Handles Ctrl-C
    Signal(SIGTSTP, SIG_DFL); // Handles Ctrl-Z
    Signal(SIGCHLD, SIG_DFL); // Handles terminated or stopped child

    destroy_job_list();
}
