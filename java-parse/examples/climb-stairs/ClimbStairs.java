public class ClimbStairs {

    public static int climbStairs0(int n) {
        int r;
        if (n <= 1) {
            r = 1;
        } else {
            int s = 2;
            int p = 1, c = 0;
            for (int i = 2; i < n; i++) {
                c = s;
                s += p;
                p = c;
            }
            r = s;
        }
        return r;
    }

    public static int climbStairs1(int n) {
        int r;
        if (n <= 1) {
            r = 1;
        } else {
            int c1 = 1;
            int c2 = 1;
            for (int i = 2; i <= n; i++) {
                int t = c2;
                c2 = t + c1;
                c1 = t;
            }
            r = c2;
        }
        return r;
    }

    public static void main(String... args) {
        System.out.println(climbStairs0(2));
        System.out.println(climbStairs1(2));
    }
}

