
#define SAMPLE_COUNT	(100 * 1000)

unsigned long nsec(void);
unsigned elapsed(unsigned long start);
bool stat_add(unsigned s);
unsigned stat_pct(float pct);
unsigned stat_count(void);
