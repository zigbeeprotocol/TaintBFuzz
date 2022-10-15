// non-terminating but non-reachable function => terminating program

int loop() {
  return loop();
}

int main() {
  return 0;
}
