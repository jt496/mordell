import
  tactic
  data.complex.basic
  ring_theory.euclidean_domain
  .rt_2_ring
  ring_theory.coprime.basic
  ring_theory.principal_ideal_domain
  number_theory.divisors
  algebra.group.units
  data.nat.prime
  ring_theory.int.basic
  algebra.ring.divisibility
  data.nat.prime_norm_num
  algebra.gcd_monoid.basic
  algebra.group.units
  algebra.group.defs
  algebra.associated


open_locale classical

--set_option profiler true


namespace ℤα
--variables (a b : ℤα)
-- #check a+b
-- #eval (⟨1,2⟩: ℤα)
-- #print instances  euclidean_domain

section mordell
parameters { x y : ℤ } (sol: x^3 = y^2 - 2)

noncomputable
instance : gcd_monoid  ℤα:=
{ gcd := λ a b, euclidean_domain.gcd a b,
  lcm := λ a b, euclidean_domain.lcm a b,
  gcd_dvd_left := λ a b, euclidean_domain.gcd_dvd_left a b,
  gcd_dvd_right := λ a b, euclidean_domain.gcd_dvd_right a b,
  dvd_gcd := λ  a b c hac hab, euclidean_domain.dvd_gcd hac hab,
  gcd_mul_lcm := begin
    intros a b,
    have h := euclidean_domain.gcd_mul_lcm a b,
    use 1,
    simp,
  end,
  lcm_zero_left := λ a, euclidean_domain.lcm_zero_left a,
  lcm_zero_right := λ a, euclidean_domain.lcm_zero_right a }

instance : is_principal_ideal_ring ℤα := infer_instance
-- #print instances is_principal_ideal_ring
-- #print instances gcd_monoid
-- #print instances is_domain

noncomputable
def d := euclidean_domain.gcd ((y:ℤα) + α) ((y:ℤα)- α)

/- 
We work towards showing that (y+α) and (y-α) are coprime, i.e.
their gcd (represented by d) is a unit. By considering the difference of the 
two terms, we find Norm d | 8. Also, x has to be odd. We have that d | x^3
which implies Norm d | x^6 (odd). This gives Norm d = 1.
-/

lemma Norm_divides {p a : ℤα} (h : p ∣ a) : (Norm p ∣ Norm a):=
  begin
  cases h with n hn,
  use Norm n,
  rw ← Norm_mul p n,
  rw hn,
  end

--Shows that the factorization of y^2-2 is valid.
lemma my_factorization: (y:ℤα)^2-2 = (y+α)*(y-α):=
begin
transitivity (y:ℤα)^2 - α^2,
congr,
rw sq_sub_sq _ _,
end

/- d = gcd (y+α) (y-α) divides the difference of
   (y+α) and (y-α), which is 2*sqrt(2). -/

lemma d_dvd_2_sqrt_2 : d ∣ 2*α :=
begin
change d ∣ α + α,
change ∃(k:ℤα), α + α = d*k,
have h : d ∣ y + α := euclidean_domain.gcd_dvd_left (y + α) (y - α),
have q : d ∣ y - α := euclidean_domain.gcd_dvd_right (y + α) (y - α),
cases h with j hj,
cases q with g hg,
use (j - g),
rw mul_sub,
rw ← hj,
rw ← hg,
rw ← sub_add,
nth_rewrite 2 add_comm,
rw add_sub_cancel (α:ℤα) (y:ℤα),
end

lemma Norm_d_dvd_eight : Norm d ∣ 8 :=
begin
have h := Norm_divides d_dvd_2_sqrt_2,
have p : Norm (2*α) = 8 := by ring_nf,
rw p at h,
exact h,
end

lemma y_mod_eight (s:ℤ) (h : y % 8 = s) : ∃(k:ℤ), y = 8*k + s :=
begin
have q := int.dvd_sub_of_mod_eq h,
cases q with l lh,
use l,
rw  ← add_right_inj (s:ℤ) at lh,
rw add_comm (s:ℤ) (y-s) at lh,
rw add_comm (s:ℤ) (8*l) at lh,
rw sub_add_cancel at lh,
exact lh,
end 

---------------------------------------------
-- Let the pain begin

lemma y_eq_zero_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 0) : false :=
begin
have t := y_mod_eight 0 p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ 64*k^2,{
use 8*k^2,
ring_nf,
},
rw sub_eq_add_neg at h,
rw dvd_add_right r at h,
rw ← dvd_abs at h,
norm_num at h,
end

lemma y_eq_one_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 1) : false :=
begin
have t := y_mod_eight 1 p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ (64*k+16)*k, {
use (8*k+2)*k,
ring_nf,
},
rw sub_eq_add_neg at h,
rw dvd_add_right r at h,
rw ← dvd_abs at h,
norm_num at h,
end

lemma y_eq_two_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 2) : false :=
begin
have t := y_mod_eight 2 p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ (64*k+32)*k, {
use (8*k+4)*k,
ring_nf,
},
rw dvd_add_right r at h,
norm_num at h,
end

lemma y_eq_three_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 3) : false :=
begin
have t := y_mod_eight 3 p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ (64*k+48)*k, {
use (8*k+6)*k,
ring_nf,
},
rw dvd_add_right r at h,
norm_num at h,
end

lemma y_eq_four_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 4) : false :=
begin
have t := y_mod_eight 4 p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ (64*k+64)*k, {
use (8*k+8)*k,
ring_nf,
},
rw dvd_add_right r at h,
norm_num at h,
end

lemma y_eq_five_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 5) : false :=
begin
have t := y_mod_eight 5 p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ (64*k+80)*k+16, {
use (8*k+10)*k+2,
ring_nf,
},
have bob : (23:ℤ) = 16 + 7 := by dec_trivial,
rw bob at h,
rw ← add_assoc at h,
rw dvd_add_right r at h,
norm_num at h,
end

lemma y_eq_six_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 6) : false :=
begin
have t := y_mod_eight 6 p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ (64*k+96)*k+32, {
use (8*k+12)*k+4,
ring_nf,
},
have bob : (34:ℤ) = 32 + 2 := by dec_trivial,
rw bob at h,
rw ← add_assoc at h,
rw dvd_add_right r at h,
norm_num at h,
end

lemma y_eq_seven_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 7) : false :=
begin
have t := y_mod_eight 7 p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ (64*k+112)*k+40, {
use (8*k+14)*k+5,
ring_nf,
},
have bob : (47:ℤ) = 40 + 7 := by dec_trivial,
rw bob at h,
rw ← add_assoc at h,
rw dvd_add_right r at h,
norm_num at h,
end

-----------------------------------------------

include sol
lemma x_odd : ¬ 2 ∣ x :=
begin
-- by_contra,
-- have k := pow_dvd_pow_of_dvd h 3,
-- have l : (2:ℤ)^3 = 8 := by norm_num,
-- rw l at k,
-- rw sol at k,

-- have : (8:ℤ) ≠ 0 := by dec_trivial,
-- have flop : 0 ≤ (8:ℤ)  := by dec_trivial,
-- have dip := int.mod_lt y this,
-- have jop := int.mod_nonneg y this,
-- rw ← abs_eq_self at flop,
-- rw flop at dip,
-- clear this flop l h sol,
-- interval_cases using jop dip,
-- exact y_eq_zero_mod_eight k h,
-- exact y_eq_one_mod_eight k h,
-- exact y_eq_two_mod_eight k h,
-- exact y_eq_three_mod_eight k h,
-- exact y_eq_four_mod_eight k h,
-- exact y_eq_five_mod_eight k h,
-- exact y_eq_six_mod_eight k h,
-- exact y_eq_seven_mod_eight k h,
sorry,
end


lemma d_dvd_x_cubed : d ∣ x^3 :=
begin
have h : d ∣ y + α := euclidean_domain.gcd_dvd_left (y + α) (y - α),
have p := dvd_mul_of_dvd_right h ((y:ℤα)-α),
rw mul_comm at p,
rw ← my_factorization at p,
norm_cast at p,
rw ← sol at p,
norm_cast,
exact p,
end

lemma Norm_d_dvd_x_six : Norm d ∣ x^6 :=
begin
have h := Norm_divides (d_dvd_x_cubed sol),
have p : (Norm x)^3 = x^6, {
  unfold Norm,
  change |x ^ 2 - 2 * 0 ^ 2| ^ 3 = x ^ 6,
  nth_rewrite 1 sq,
  rw mul_zero,
  rw mul_zero,
  rw sub_zero,
  rw abs_sq,
  rw ← pow_mul,
  have : 6 = 2*3 := by dec_trivial,
  rw ← this,
},
rw pow_three at p,
rw ← Norm_mul at p,
rw ← Norm_mul at p,
rw ← pow_three at p,
rwa p at h,
end

lemma x_pow_six_odd : ¬ 2 ∣ x^6 :=
begin
by_contra,
apply x_odd sol,
exact prime.dvd_of_dvd_pow int.prime_two h,
end

lemma x_pow_six_really_odd : odd (x^6) :=
begin
have h := x_pow_six_odd sol,
rw int.two_dvd_ne_zero at h,
rwa ← int.odd_iff at h,
end
omit sol

lemma of_dvd_int {m n : ℤ} (hn : odd n) (hm : m ∣ n) : odd m :=
begin
cases hn with k hk,
cases hm with j hj,
by_contra,
rw ← int.even_iff_not_odd at h,
cases h with b hb,
rw hj at hk,
rw hb at hk,
rw ← two_mul at hk,
rw add_comm at hk,
have p := sub_eq_of_eq_add hk,
rw mul_assoc at p,
rw ← mul_sub at p,
rw mul_comm at p,
have jeff := dvd_of_mul_left_eq (b * j - k) p,
norm_num at jeff,
end

include sol
lemma Norm_d_odd : odd (Norm d) :=
begin
exact of_dvd_int (x_pow_six_really_odd sol) (Norm_d_dvd_x_six sol),
end

#eval nat.divisors 8

lemma divisors_of_eight {k : ℤ} (h : k ∣ 8) (p : 0 ≤ k): k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 :=
begin
have hl : (0:ℤ) < 8 := by dec_trivial,
have hp := int.le_of_dvd hl h,
clear hl,
have m : k < 9,
linarith,
clear hp,
cases k with k' k'',
work_on_goal 2
{
  have := int.neg_succ_of_nat_lt_zero k'',
  exfalso,
  sorry
},
change (k':ℤ) ∣ (8:ℕ) at h,
rw [int.coe_nat_dvd] at h,
have := (@nat.mem_divisors k' 8).2 ⟨h, dec_trivial⟩,
fin_cases this;
simp only [int.of_nat_eq_coe, int.coe_nat_bit0, algebra_map.coe_one, eq_self_iff_true, true_or, or_true],
-- have r := nat.divisors_prime_pow nat.prime_two 3,
-- norm_num at r,
end 

lemma Norm_d_eq_one : Norm d = 1 :=
begin
have h := Norm_d_dvd_eight,
have p := Norm_d_odd sol,
have easy : 0 ≤ Norm d := abs_nonneg _,
have q := divisors_of_eight sol h easy,
cases q,{
exact q,
},
cases q,{
  exfalso,
  rw q at p,
  norm_num at p,
},
cases q,{
  rw q at p,
  norm_num at p,
},
rw q at p,
norm_num at p,
end


end mordell
end ℤα 