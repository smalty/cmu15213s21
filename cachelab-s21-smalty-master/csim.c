/* Name: Edric Eun
 * Andrew: eeun
 *
 * File Description: Simulates a cache given number of set index bits,
 * number of lines per set, number of block bits, and trace file. The
 * trace file must contain lines in the form "Op Address,Size" where
 * Op indicates Load or Store, Address is the address accessed, and Size
 * is the number of bytes accessed.
 *
 * Input: -s (set), -E (lines per set), -b (block), -t (trace file)
 *
 * Output: Print summary of number of hits, misses, evictions, dirty bytes still
 * in cache, and dirty bytes evicted
 */

#include "cachelab.h"
#include <getopt.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/*MAX is a large number*/
#define MAX 100
#define HEX_BASE 16
#define ADDR_START_INDEX 2

typedef struct {
    int v;        /* valid bit */
    int d;        /* dirty bit */
    long int tag; /* tag */
    int time;     /* time last used */
} block_t;

/*Function to generate a bitMask*/
int genMask(int highbit, int lowbit) {
    return (1 << highbit) - (1 << lowbit);
}
/*Least recently used system takes in row from cache and returns index of
smallest time*/
int lru(block_t **cache_set, int E_size) {
    int cur_time = cache_set[0]->time;
    int cur_index = 0;
    for (int j = 0; j < E_size; j++) {
        if (cache_set[j]->time < cur_time) {
            cur_time = cache_set[j]->time;
            cur_index = j;
        }
    }
    return cur_index;
}
/*Function to free cache*/
void freeCache(block_t ***cache, int set_size, int E_size) {
    for (int i = 0; i < set_size; i++) {
        for (int j = 0; j < E_size; j++) {
            free(cache[i][j]);
        }
        free(cache[i]);
    }
    free(cache);
}
/*Simulate Cache. Each line in the cache has type block_t* and contains
 * values v (valid bit), d (dirty bit), tag (tag), and time (time when last
 * used)
 */
csim_stats_t *simulateCache(block_t ***cache, FILE *trace_file, int s_size,
                            int E_size, int b_size) {

    int block_size = 1 << b_size;

    char line[MAX];

    /*Malloc stats and Initialize*/
    csim_stats_t *stats = malloc(sizeof(csim_stats_t));
    stats->hits = 0;
    stats->dirty_bytes = 0;
    stats->dirty_evictions = 0;
    stats->evictions = 0;
    stats->misses = 0;

    /*Initial time is 0*/
    int time = 0;

    /*Loop through each line in file*/
    while (fgets(line, MAX, trace_file) != NULL) {
        char op = line[0];
        size_t addr_length = 0;
        char addr_str[MAX];
        int addr_i = ADDR_START_INDEX;

        /*Extract the address and put it in addr_str*/
        while (line[addr_i] != ',') {
            addr_str[addr_length] = line[addr_i];
            addr_length += 1;
            addr_i += 1;
        }
        addr_str[addr_length] = '\0';
        long addr = 0;

        /*Take the hex string and convert it into an base 10 int in addr*/
        sscanf(addr_str, "%lx", &addr);

        /*Generate mask to extract the set bits*/
        int sMask = genMask(s_size + b_size, b_size);

        /*Using sMask, extract s and from s, extract tag by subtracting
        from addr*/
        unsigned long int s = (addr & sMask) >> b_size;
        unsigned long int tag = (addr - s) >> (s_size + b_size);

        /*Loop through the set and look for a line with tag. If a line is
        found with the same tag, set set_i to the index of that line, otherwise
        set_i is E_size.*/
        int set_i = E_size;
        for (int j = 0; j < E_size; j++) {
            if (cache[s][j]->tag == tag && j < set_i) {
                printf("cache:%ld input:%ld \n", cache[s][j]->tag, tag);
                set_i = j;
            }
        }
        /*If a line with the same tag is found, update hit, time, and if
        possible, dirt bit.*/
        if (set_i != E_size) {
            stats->hits += 1;
            cache[s][set_i]->time = time;
            if (op == 'S' && cache[s][set_i]->d == 0) {
                cache[s][set_i]->d = 1;
                stats->dirty_bytes += block_size;
            }
        } else {
            /*If a line with the same tag is not found, look for a free space
            in the cache.*/
            set_i = E_size;
            for (int j = 0; j < E_size; j++) {
                if (cache[s][j]->v == 0 && j < set_i) {
                    set_i = j;
                }
            }
            /*If a free space is found, load the address in and update valid
            bit, tag, time, and if possible, dirty bit.*/
            if (set_i != E_size) {
                stats->misses += 1;
                cache[s][set_i]->v = 1;
                cache[s][set_i]->tag = tag;
                cache[s][set_i]->time = time;
                if (op == 'S') {
                    cache[s][set_i]->d = 1;
                    stats->dirty_bytes += block_size;
                }
            } else {
                /*No free space is found, so lru_i (index of least recently
                used line) is found and replaced. If the line at index lru_i
                is dirty, update dirty eviction. Update dirty bit depending
                on operation.*/
                int lru_i = lru(cache[s], E_size);
                if (cache[s][lru_i]->d == 1) {
                    stats->dirty_evictions += block_size;
                    stats->dirty_bytes -= block_size;
                }
                cache[s][lru_i]->tag = tag;
                cache[s][lru_i]->time = time;
                if (op == 'S') {
                    cache[s][lru_i]->d = 1;
                    stats->dirty_bytes += block_size;
                } else {
                    cache[s][lru_i]->d = 0;
                }
                stats->misses += 1;
                stats->evictions += 1;
            }
        }
        /*Increment time*/
        time += 1;
    }
    return stats;
}

int main(int argc, char *argv[]) {
    /*Initialize values needed in getopt*/
    FILE *trace_file = NULL;
    extern char *optarg;
    extern int optind, opterr, optopt;

    int s_size = 0;
    int E_size = 0;
    int b_size = 0;

    char opt;

    while ((opt = getopt(argc, argv, "s:E:b:t:")) != -1) {
        switch (opt) {
        case 's':
            s_size = atoi(optarg);
            break;
        case 'E':
            E_size = atoi(optarg);
            break;
        case 'b':
            b_size = atoi(optarg);
            break;
        case 't':
            trace_file = fopen(optarg, "r");
            break;
        default:
            printf(optarg);
        }
    }

    /*Case if trace_file is not loaded*/
    if (trace_file == NULL) {
        printf("Error reading file \n");
        exit(1);
    } else {
        /*Allocate memory for a cache with 2^s rows of lines (type block_t) and
        E columns. Initialize values of the lines.*/
        int set_size = 1 << s_size;

        block_t ***cache = malloc(set_size * sizeof(block_t **));
        for (int i = 0; i < set_size; i++) {
            cache[i] = malloc(E_size * sizeof(block_t *));
            for (int j = 0; j < E_size; j++) {
                cache[i][j] = malloc(sizeof(block_t));
                cache[i][j]->v = 0;
                cache[i][j]->d = 0;
                cache[i][j]->tag = -1;
                cache[i][j]->time = 0;
            }
        }

        csim_stats_t *stats =
            simulateCache(cache, trace_file, s_size, E_size, b_size);

        /*Print summary of stats*/
        printSummary(stats);

        /*Free cache and stats*/
        freeCache(cache, set_size, E_size);
        free(stats);
    }

    return 0;
}