#include <err.h>
#include <time.h>
#include <stdlib.h>
#include <stdbool.h>

#include "glue_hdr.h"

static unsigned sample[SAMPLE_COUNT];
static unsigned n_samples, sorted;

unsigned long
nsec(void)
{
	struct timespec ts;

	clock_gettime(CLOCK_MONOTONIC, &ts);
	return ts.tv_sec * 1000000000UL + ts.tv_nsec;
}

unsigned
elapsed(unsigned long start)
{
	return nsec() - start;
}

bool
stat_add(unsigned s)
{
	if (n_samples == SAMPLE_COUNT)
		return false;
	sample[n_samples++] = s;
	return true;
}

static int
cmp(const void *a, const void *b)
{
	return *(int *)a - *(int *)b;
}

static void
sort_samples(void)
{
	if (sorted == n_samples)
		return;
	qsort(sample, n_samples, sizeof(sample[0]), cmp);
	sorted = n_samples;
}

unsigned
stat_pct(float pct)
{
	int idx;

	idx = (pct / 100.0)  * (n_samples - 1);
	sort_samples();
	return sample[idx];
}

unsigned
stat_count(void)
{
	return n_samples;
}
