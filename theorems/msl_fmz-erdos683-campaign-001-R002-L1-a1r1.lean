set_option autoImplicit false

def isPrime (n : Nat) : Bool := n >= 2 && (List.range (n+1) |>.filter (fun d => d >= 2 && d ∣ n)).length == 1

def lpf (n : Nat) : Nat :=
  ((List.range (n+1)).filter (fun d => d >= 2 && d ∣ n && isPrime d)).foldl max 0

-- Endpoint check for fixed c = 1 (any fixed c > 0 works the same way):
-- k = 1   : C(n,1) = n, bound = min(n-1+1, 1^(1+c)) = min(n, 1) = 1
-- k = n-1 : C(n,n-1) = n, bound = min(2, (n-1)^(1+c)) = 2 since n >= 2
-- So the fragment holds iff lpf n >= 1 and lpf n >= 2 for all 2 <= n <= N.

def endpointCheck (N : Nat) : Bool :=
  (List.range (N-1)).all (fun i =>
    let n := i + 2
    lpf n >= min n 1 && lpf n >= min 2 ((n-1)*(n-1)))

theorem msl_fmz_erdos683_campaign_001_R002_L1_a1r1  : endpointCheck 60 = true := by decide
