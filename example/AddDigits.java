class AddDigits {
  // https://leetcode.com/problems/add-digits/discuss/68622
  public static int addDigits1(int n){
    if(n==0)
      return 0;
    return n + addDigits1(n/10);
  }

  // https://leetcode.com/problems/add-digits/discuss/68588
  public static int addDigits2(int num) {
    return num==0?0:(num%9==0?9:(num%9));
  }

  // https://leetcode.com/problems/add-digits/discuss/68689
  public static int addDigits3(int num) {
    int cur = num;
    int sum = 0;
    boolean oneDigit = false;
    while (!oneDigit) {
      while (cur/10 != 0) {
        sum += cur;
        cur = cur/10;
      }
      sum += cur;
      if (sum/10 == 0)
        oneDigit = true;
      else {
        cur = sum;
        sum = 0;
      }
    }
    return sum;
  }
}
