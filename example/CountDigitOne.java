class CountDigitOne {
  // https://leetcode.com/problems/number-of-digit-one/discuss/64397
  public static int countDigitOne1(int n) {
    if (n < 1) {
      return 0;
    } else if(n >= 1 && n < 10) {
      return 1;
    } else {
      int y=1, x=n;
      while (!(x < 10)){
        x /= 10;
        y *= 10;
      }
      if (x == 1)
        return n - y + 1 + countDigitOne1(y - 1) + countDigitOne1(n % y);
      else
        return y + x*countDigitOne1(y - 1) + countDigitOne1(n % y);
    }
  }

  // https://leetcode.com/problems/number-of-digit-one/discuss/64390
  public static int countDigitOne2(int n) {
    int count = 0;
    for (long k = 1; k <= n; k *= 10) {
      long r = n / k, m = n % k;
      count += (r + 8) / 10 * k + (r % 10 == 1 ? m + 1 : 0);
    }
    return count;
  }
}
