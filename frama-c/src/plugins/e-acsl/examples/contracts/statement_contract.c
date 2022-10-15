#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>

int main() {
    int value, sign, result;

    srand(time(NULL));
    value = rand();
    sign = rand();
    if (sign % 2) {
        value = -value;
    }

    /*@
        requires value > INT_MIN;
        assigns result;
        ensures result >= 0;

        behavior pos:
            assumes value >= 0;
            ensures result == value;

        behavior neg:
            assumes value < 0;
            ensures result == -value;

        complete behaviors;
        disjoint behaviors;
    */
    if (value < 0) {
        result = -value;
    } else {
        result = value;
    }

    printf("Value: %d, Result: %d\n", value, result);

    return 0;
}

