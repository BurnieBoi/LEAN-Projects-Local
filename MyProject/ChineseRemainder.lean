--due to the fundementals of type theory, the chinese remainder theorem can not be solved
-- in the way I was attempting to here

import mathlib

theorem AsianLeftoversfor2 {m1 m2 x0 a1 a2 k: ℤ}(g1:IsCoprime m1 m2 )(g2:m1>0) (g3:m2>0) (g2b: m1 ≠ 0) (g3b: m2 ≠ 0)
(g4: m=m1*m2) (g7:t1=(m1.toNat).totient )(g8:t2 = (m2.toNat).totient):∃x0,(x0 % m1=a1 % m1 ∧ x0%m2 =a2 % m2)∧ ∀k, ((k*m+x0)=a1.mod m1 ∧ (k*m+x0)=a2.mod m2)
:= by
have h1: IsCoprime m2 m1
apply IsCoprime.symm
exact g1
have h2: (m1.toNat)^(t2-1)*(m1.toNat) % m2.toNat = 1 % m2.toNat
rw[pow_sub_one_mul, g8]
rw[Nat.ModEq.pow_totient]
apply IsCoprime.nat_coprime
simp
rw[Int.max_eq_left]
rw[Int.max_eq_left]
exact g1
apply le_of_lt
apply g3
apply le_of_lt
apply g2
rw[g8]
simp
apply g3
have h3:  m2.toNat^(t1-1)*m2.toNat % m1.toNat= 1 % m1.toNat
rw[pow_sub_one_mul, g7]
rw[Nat.ModEq.pow_totient]
apply IsCoprime.nat_coprime
simp
rw[Int.max_eq_left]
rw[Int.max_eq_left]
apply h1
apply le_of_lt
apply g2
apply le_of_lt
apply g3
rw[g7]
simp
apply g2
have h3b: 1 % m1 = 1 % m1.toNat
simp
rw[Int.max_eq_left]
apply le_of_lt
trivial
let b1 := m2.toNat^(t1-1)
let b2 := m1.toNat^(t2-1)
let x1:=m2.toNat*b1*a1
let x2:=m1.toNat*b2*a2
let x:= x1+x2
have h4:  m1.toNat * b2 * a2 % m1.toNat = 0 % m1.toNat
simp
repeat apply dvd_mul_of_dvd_left
simp
have h4b:  m2.toNat * b1 * a1 % m2.toNat = 0 % m2.toNat
simp
repeat apply dvd_mul_of_dvd_left
simp
have h5: x2 % m1.toNat = 0 % m1.toNat
apply Int.ModEq.trans
dsimp [x2]
apply h4
trivial
have h5b:x1 % m2.toNat = 0 % m2.toNat
apply Int.ModEq.trans
dsimp [x2]
apply h4b
trivial
have hn: x % m1.toNat= a1 % m1.toNat ∧ x % m2.toNat = a2 % m2.toNat
constructor
dsimp[x]
rw[Int.add_emod]
rw[h5]
dsimp[x1]
dsimp[b1]
rw[add_zero]
rw[Int.mul_emod]
rw[mul_comm] at h3
rw[← Nat.cast_mul]
