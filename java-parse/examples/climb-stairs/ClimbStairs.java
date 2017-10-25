public class ClimbStairs {

    public static int climbStairs0(int n) {
        int result = 0;
        if (n <= 1) {
            result = 1;
        } else {
            int sum = 2;
            int prev = 1, cur = 0;
            for (int i = 2; i < n; i++) {
                cur = sum;
                sum += prev;
                prev = cur;
            }
            result = sum;
        }
        return result;
    }

    public static int climbStairs1(int n) {
        int result = 0;
        if (n <= 1) {
            result = 1;
        } else {
            int count1 = 1;
            int count2 = 1;
            for (int i = 2; i <= n; i++) {
                int temp = count2;
                count2 = temp + count1;
                count1 = temp;
            }
            result = count2;
        }
        return result;
    }

    public static void main(String... args) {
        System.out.println(climbStairs0(2));
        System.out.println(climbStairs1(2));
    }
}

