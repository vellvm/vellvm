void printf_polymorphism_for_free() {
    printf("In C, %d can be %c or %x or even %o.\n", 48, 48, 48, 48);
}

int main() {
    printf_polymorphism_for_free();
}