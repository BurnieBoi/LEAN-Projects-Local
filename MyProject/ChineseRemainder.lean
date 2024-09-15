import mathlib

theorem AsianLeftoversfor2 {x0 a1 a2 k: ℤ} {m1 m2 : ℕ } (g1:m1.gcd m2 = 1)(g2:m1>0) (g3:m2>0)
(g4: m=m1*m2):∃x0, (x0=a1.bmod m1 ∧ x0=a2.bmod m2)∧ ∀k, ((k*m+x0)=a1.bmod m1 ∧ (k*m+x0)=a2.bmod m2)
:= by


-- Prove that there exists b1 and b2 such that m1*b2=1 mod m2 and m2*b1=1 mod m1
-- Then prove that m2b1a1+m1b2a2 is an integer, and that it is x0
-- Then prove the last part



-- I think induction can be used very easily to generalize this for n a's and m's,
-- but I want to do this base case first
