#include <assert.h>
#include <stdint.h>

extern int64_t sonatina_counter;
extern int64_t sonatina_bss;
extern const int64_t sonatina_constant;
extern int64_t *sonatina_update(int64_t *, int64_t);
extern uint32_t sonatina_xor32(uint32_t, uint32_t);
extern int64_t sonatina_aggregate_wrapper(int64_t, int64_t, int64_t *);

int64_t host_counter = 5;

int64_t host_mix(int64_t a, int64_t b) { return a * 3 + b; }
int64_t *host_offset(int64_t *p, int64_t count) { return p + count; }
uint32_t host_xor32(uint32_t a, uint32_t b) { return a ^ b; }

int main(void) {
    assert(sonatina_counter == 10);
    assert(sonatina_bss == 0);
    assert(sonatina_constant == -77);
    int64_t values[] = {11, -1, 0x1234};
    assert(sonatina_update(values, 7) == &values[1]);
    assert(values[0] == 11 && values[1] == 40 && values[2] == 0x1234);
    assert(sonatina_counter == 15 && sonatina_bss == 40 && host_counter == 6);
    sonatina_counter = 100;
    host_counter = 9;
    assert(sonatina_update(values, -4) == &values[1]);
    assert(values[1] == 29);
    assert(sonatina_counter == 109 && sonatina_bss == 29 && host_counter == 10);
    assert(sonatina_xor32(UINT32_C(0xfedcba98), UINT32_C(0x12345678)) == UINT32_C(0xece8ece0));
    int64_t output = 0;
    assert(sonatina_aggregate_wrapper(INT64_C(0x123456789abcdef), -99, &output) == 0);
    assert(output == -99);
    return 0;
}
