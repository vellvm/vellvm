int complexcall(int x, int y) {
    if (x == 0)   
        return y;
    return 2 * complexcall(complexcall(x - 1, y), 0);
}

int main() {
    int x = complexcall(1, 2);
    int z = complexcall(4, 8) >> 4;
    return 0;
}