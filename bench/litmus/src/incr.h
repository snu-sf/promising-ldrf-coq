void incr(uint64_t n);
void incr_load(uint64_t n);
void incr_store(uint64_t n);

uint64_t xchg(uint64_t n);
uint64_t xchg_load(uint64_t n);
uint64_t xchg_store(uint64_t n);

uint64_t load(uint64_t n);
uint64_t load_store(uint64_t n);
uint64_t load_unroll(uint64_t n);
uint64_t load_store_unroll(uint64_t n);

void incr_unroll(uint64_t n);
void incr_load_unroll(uint64_t n);
void incr_store_unroll(uint64_t n);

uint64_t xchg_unroll(uint64_t n);
uint64_t xchg_load_unroll(uint64_t n);
uint64_t xchg_store_unroll(uint64_t n);
