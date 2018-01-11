class TrailingZeroes {
  // https://leetcode.com/problems/factorial-trailing-zeroes/discuss/52428
  public static int trailingZeroes1(int n) {
    int nn = n;
    int count = 0;
    while(nn > 0) {
      nn /= 5;
      count += nn;
    }
    return count;
  }

  // https://leetcode.com/problems/factorial-trailing-zeroes/discuss/52452
  public static int trailingZeroes2(int n) {
    if(n < 5) return 0;
    return n / 5 + trailingZeroes2(n / 5);
  }
}
