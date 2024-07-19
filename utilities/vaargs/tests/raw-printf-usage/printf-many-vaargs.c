// also makes sure clang is hip to %% syntax
void printf_fortminor() {
    printf(
"This is %d%% percent luck \
\n%d%% percent skill \
\n%d%% percent concentrated power of will \
\n%d%% percent pleasure \
\n%d%% percent pain \
\nAnd %d%% reason to remember the name.\n", 10, 20, 15, 5, 50, 100);
}

int main() {
    printf_fortminor();
}