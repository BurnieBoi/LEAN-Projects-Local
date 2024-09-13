import mathlib

def f (x:Nat) :=  x

theorem nonsquare_comp_div_pred_fac {a b: ℕ } (g1: a>2) (g2:b>2):
 ∏ c ∈ ({a} ∪ {b}), f c ∣ ∏ c ∈ (Finset.range (a*b)), f c := by
have h1: a>0
apply gt_trans
exact g1
simp
have h2: b>0
apply gt_trans
exact g2
simp
have h3: a<a*b
apply lt_mul_right
exact h1
apply gt_trans
exact g2
simp
have h4: b<a*b
apply lt_mul_left
exact h2
apply gt_trans
exact g1
simp
have h5: {a} ∪ {b} ⊆ Finset.range (a*b)
rw[Finset.union_subset_iff]
simp
constructor
exact h3
exact h4
apply Finset.prod_dvd_prod_of_subset
exact h5

theorem sqr_comp_dvd_pred_fac {a: ℕ }(g1:2<a):
∏ c ∈ {a^2}, f c ∣ ∏ c ∈ (Finset.range (a^2)), f c := by
have h1: a^1<a^2
have h2: 1<2
simp
apply pow_lt_pow_right
apply lt_trans
apply h2
exact g1
simp
have h3: a<a^2
have h4: a<a^2 ↔ a^1<a^2
simp
rw[h4]
exact h1
have h5: 2*a<a^2
rw[pow_two]
rw[mul_lt_mul_right]
exact g1
apply lt_trans
have h6: 0<2
simp
exact h6
exact g1
have hn: {a} ∪ {2*a} ⊆ Finset.range (a^2)
rw[Finset.union_subset_iff]
simp
constructor
apply h3
apply h5
have h2n:∏ c ∈ ({a^2}), f c ∣ ∏ c ∈ ({a} ∪ {2*a}), f c
rw[Finset.prod_union]
repeat rw[Finset.prod_singleton]
repeat rw[f]
ring_nf
apply dvd_mul_right
simp
rw[two_mul]
rw[add_right_eq_self]
apply ne_of_gt
apply gt_trans
apply g1
repeat simp
have h3n: ∏ c ∈ ({a} ∪ {2*a}), f c ∣ ∏ c ∈ (Finset.range (a^2)), f c
apply Finset.prod_dvd_prod_of_subset
apply hn
apply dvd_trans
simp at h2n
apply h2n
apply h3n
