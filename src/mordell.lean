import
  tactic
  data.complex.basic
  ring_theory.euclidean_domain
  .rt_7_ring
  ring_theory.coprime.basic
  ring_theory.principal_ideal_domain
  number_theory.divisors
  algebra.group.units
  data.nat.prime
  ring_theory.int.basic
  data.int.order.basic
  data.int.modeq
  algebra.ring.divisibility
  data.int.dvd.pow


  

namespace ℤα
variables (a b : ℤα)
#check a+b
#eval (⟨1,2⟩: ℤα)
#print instances  euclidean_domain

open complex

open euclidean_domain

section mordell
parameters { x y : ℤ } {sol: x^3 = y^2 - y + 2}

instance : is_principal_ideal_ring ℤα := infer_instance
#print instances is_principal_ideal_ring

#print instances normalized_gcd_monoid

noncomputable
def d := gcd ((y:ℤα)-α) ((y:ℤα)-α_bar)

lemma conj_α: star_ring_end ℂ complex_α = α_bar :=
  begin
  unfold α_bar complex_α,
  have h : star_ring_end ℂ ⟨1/2, (rt_7/2)⟩ = ⟨1/2, -rt_7/2⟩ := by ring_nf,
  rw h,
  clear h,
  have p := re_of_coe,
  have q := im_of_coe,
  specialize p (⟨1, -1⟩:ℤα),
  specialize q (⟨1, -1⟩:ℤα),
  simp at p q,
  ring_nf at p,
  ext,
  rw p,
  rw q,
  end 

  lemma nat_norm_divides (a p : ℤα):
  (p ∣ a) → (nat_Norm p ∣ nat_Norm a):=
  begin
  intro h,
  cases h with n hn,
  use nat_Norm n,
  rw ← nat_Norm_mul p n,
  rw hn,
  end

  lemma norm_divides (a p : ℤα):
  (p ∣ a) → (Norm p ∣ Norm a):=
  begin
  intro h,
  cases h with n hn,
  use Norm n,
  rw ← Norm_mul p n,
  rw hn,
  end

lemma coe_from_ints (a:ℤ) : (a:ℤα) = (⟨a, 0⟩:ℤα) :=
begin
unfold_coes,

sorry,
end

--Shows that the factorization of y^2-y+2 is valid.
lemma my_factorization:
  (y:ℤα)^2-y+2 = (y-α)*(y-α_bar):=
  begin
  transitivity (y:ℤα)^2 - (α+α_bar)*y + α*α_bar, {
    congr,
    have r : α + α_bar = one := by ring_nf,
    rw r,
    have q : one*(y:ℤα)=(y:ℤα) := my_one_mul (y:ℤα),
    rw q,
  },
  ring_nf,
  end

lemma d_dvd_sqrt_seven_i : d ∣ α - α_bar :=
begin
change ∃(k:ℤα), α - α_bar = d*k,
have h : d ∣ y - α := gcd_dvd_left (y - α) (y - α_bar),
have q : d ∣ y - α_bar := gcd_dvd_right (y - α) (y - α_bar),
cases h with j hj,
cases q with g hg,
use (g - j),
rw mul_sub,
rw ←  hg,
rw ← hj,
ring_nf,
end

lemma norm_seven : Norm (α - α_bar) = 7 :=
begin
unfold Norm α α_bar,
ring_nf,
end

--Why is it showing y:ℤ as a hypothesis?
lemma nd_dvd_seven : Norm d ∣ 7 :=
begin
have h := d_dvd_sqrt_seven_i,
have q := norm_divides (α - α_bar) d h,
rw norm_seven at q,
exact q,
end

lemma nat_nd_dvd_seven : nat_Norm d ∣ 7 :=
begin
have h := nd_dvd_seven,
rw equiv_norms at h,
exact_mod_cast h,
end

lemma seven_prime : nat.prime 7 :=
begin
sorry,
end


lemma nat_nd_one_or_seven : nat_Norm d = 1 ∨ nat_Norm d = 7 :=
begin
exact nat.prime.eq_one_or_self_of_dvd (seven_prime) (nat_Norm d) (nat_nd_dvd_seven),
end

lemma nd_one_or_seven : Norm d = 1 ∨ Norm d = 7 := begin
have h := nat_nd_one_or_seven,
cases h with p q,
left,
rw equiv_norms,
exact_mod_cast p,
right,
rw equiv_norms,
exact_mod_cast q,
end


lemma norm_y_minus_α : Norm (y-α) = y^2 - y + 2 :=
begin
have h : (y:ℤα) - α = (⟨y,-1⟩:ℤα), {
rw coe_from_ints,
unfold α,
change add (⟨y, 0⟩:ℤα) (⟨0, 1⟩:ℤα).neg = {x := y, y := -1},
have r : neg (⟨0, 1⟩:ℤα) = (⟨0,-1⟩:ℤα) := by refl,
rw r,
have p : add (⟨y, 0⟩:ℤα) (⟨0,-1⟩:ℤα) = (⟨y+0,0+(-1)⟩:ℤα) := by refl,
rw p,
norm_num,
},
rw h,
unfold Norm,
ring_nf,
end

-- Using the fact that d divides y-α
lemma nd_dvd_pol : Norm d ∣ y^2 - y + 2 :=
begin
rw ← norm_y_minus_α,
apply norm_divides,
exact gcd_dvd_left (y - α) (y - α_bar),
end

-- assuming N(d) = 7
-- find mathlib lemma for y % 7 = 4 → ∃k, y = 7k+4
-- use interval_cases and the above lemmas
lemma y_mod_seven (s:ℤ) (h : y % 7 = s) : ∃(k:ℤ), y = 7*k + s :=
begin
have q := int.dvd_sub_of_mod_eq h,
cases q with l lh,
use l,
linarith,
end 

lemma y_eq_zero_mod_seven (h : 7 ∣ y^2 - y + 2) (p : y % 7 = 0) : false :=
begin
have t := y_mod_seven 0 p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 7 ∣ ((49 * k - 7) * k),
{
use (7*k*k - k),
ring_nf,
},
rw dvd_add_right r at h,
have j : (0:ℤ) < 2 := by linarith,
have g := int.le_of_dvd j h,
linarith,
end

lemma y_eq_one_mod_seven (h : 7 ∣ y^2 - y + 2) (p : y % 7 = 1) : false :=
begin
have t := y_mod_seven 1 p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 7 ∣ ((49 * k + 7) * k),
{
use (7*k*k + k),
ring_nf,
},
rw dvd_add_right r at h,
have j : (0:ℤ) < 2 := by linarith,
have g := int.le_of_dvd j h,
linarith,
end

lemma y_eq_two_mod_seven (h : 7 ∣ y^2 - y + 2) (p : y % 7 = 2) : false :=
begin
have t := y_mod_seven 2 p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 7 ∣ ((49 * k + 21) * k),
{
use (7*k*k + 3*k),
ring_nf,
},
rw dvd_add_right r at h,
have j : (0:ℤ) < 4 := by linarith,
have g := int.le_of_dvd j h,
linarith,
end

lemma y_eq_three_mod_seven (h : 7 ∣ y^2 - y + 2) (p : y % 7 = 3) : false :=
begin
have t := y_mod_seven 3 p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have c : (8:ℤ) = 7*1 + 1 := by linarith,
nth_rewrite 1 c at h,
have r : 7 ∣ ((49 * k + 35) * k + 7),
{
use (7*k*k + 5*k + 1),
ring_nf,
},
rw ← add_assoc at h,
rw mul_one at h,
rw dvd_add_right r at h,
have j : (0:ℤ) < 1 := by linarith,
have g := int.le_of_dvd j h,
linarith,
end

lemma y_eq_five_mod_seven (h : 7 ∣ y^2 - y + 2) (p : y % 7 = 5) : false :=
begin
have t := y_mod_seven 5 p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have c : (22:ℤ) = 7*3 + 1 := by linarith,
rw c at h,
have r : 7 ∣ ((49 * k + 63)*k + 7*3),
{
  use (7*k*k + 9*k + 3),
  ring_nf,
},
rw ← add_assoc at h,
rw dvd_add_right r at h,
have j : (0:ℤ) < 1 := by linarith,
have g := int.le_of_dvd j h,
linarith,
end

lemma y_eq_six_mod_seven (h : 7 ∣ y^2 - y + 2) (p : y % 7 = 6) : false :=
begin
have t := y_mod_seven 6 p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have c : (32:ℤ) = 7*4 + 4 := by linarith,
rw c at h,
have r : 7 ∣ ((49 * k + 77)*k + 7*4),
{
 use (7*k*k + 11*k + 4),
 ring_nf,
},
rw ← add_assoc at h,
rw dvd_add_right r at h,
have j : (0:ℤ) < 4 := by linarith,
have g := int.le_of_dvd j h,
linarith,
end


lemma seven_dvd_pol (mn : Norm d = 7) : y % 7 = 4 :=
begin
have h : 7 ∣ y^2 - y + 2, {
  rw ← mn,
  exact nd_dvd_pol,
},
have : (7:ℤ) ≠ 0 := by linarith,
have g : 0 ≤  (7:ℤ)  := by linarith,
have k := int.mod_lt y this,
have j := int.mod_nonneg y this,
rw  ← abs_eq_self at g,
rw g at k,
interval_cases using j k,
{
  exfalso,
  exact y_eq_zero_mod_seven h h_1,
},

exfalso,
exact y_eq_one_mod_seven h h_1,

exfalso,
exact y_eq_two_mod_seven h h_1,

exfalso,
exact y_eq_three_mod_seven h h_1,

exact h_1,

exfalso,
exact y_eq_five_mod_seven h h_1,

exfalso,
exact y_eq_six_mod_seven h h_1,
end

lemma stuff_bro (h : Norm d = 7) : 7 ∣ x^3 :=
begin
have h : 7 ∣ y^2 - y + 2, {
  rw ← h,
  exact nd_dvd_pol,
},
sorry,
end

lemma sev_dvd_x_cubed (h : 7 ∣ x^3) : 7 ∣ x :=
begin
--suprising?
have p := int.prime.dvd_pow' (seven_prime) (h),
exact_mod_cast p,
end

lemma seven_sq_dvd (h : 7 ∣ x) : (7^2 ∣ x^3) :=
begin
have p := pow_dvd_pow_of_dvd h 3,
cases p with f hf,
use 7*f,
linarith,
end

lemma seven_sq_dvd_sol (h : Norm d = 7) : (7^2 ∣ x^3) :=
begin
apply seven_sq_dvd,
apply sev_dvd_x_cubed,
apply stuff_bro,
exact h,
end

lemma seven_sq_negdvd (h : y % 7 = 4) (p : 7^2 ∣ y^2 - y +2) : false:=
begin
have q := y_mod_seven 4 h,
cases q with r hr,
rw hr at p,
ring_nf at p,
have g : 49 ∣ ((49 * r + 49)*r),
{
  use (r*r + r),
  ring_nf,
},
rw dvd_add_right g at p,
have j : (0:ℤ) < 14 := by linarith,
have t := int.le_of_dvd j p,
linarith,
end

lemma seven_sq_negdvd_full (h : Norm d = 7) (p : 7^2 ∣ y^2 - y + 2) : false:=
begin
have q := seven_dvd_pol h,
exact seven_sq_negdvd q p,
end

lemma nd_eq_one : Norm d = 1 :=
begin
have h := nd_one_or_seven,
cases h with t f,
exact t,
exfalso,
have lick := seven_sq_dvd_sol f,
exact seven_sq_negdvd_full f lick,
sorry,
end

lemma unit_if_norm_one (a : ℤα) : is_unit a → nat_Norm a = 1 :=
begin
intro h,
rw is_unit_iff_exists_inv at h,
have p : ∃ (b : ℤα), 1 = a * b := by tauto,
change a ∣ 1 at p,
have l := nat_norm_divides 1 a p,
have d : nat_Norm 1 = 1 := by ring,
rw d at l,
rwa nat.dvd_one at l,
end

lemma fac_this (n m : ℤ) : 4*(n^2 + n*m + 2 * m^2) = (2*n + m)^2 + 7*m^2 :=
begin
ring_nf,
end

lemma sq_tauto (a:ℤ) : a^2 = 0 ∨ a^2 > 0 :=
begin
by_contra,
rw not_or_distrib at h,
cases h with p q,
apply q,
have r : a ≠ 0 := by finish,
exact sq_pos_of_ne_zero a r,
end

lemma units_are {a:ℤα} (k : nat_Norm a = 1): a = 1 ∨ a = -1 := 
begin
have q : Norm a = 1, {
  rw equiv_norms,
  exact_mod_cast k,
},
unfold Norm at q,
have r : (4:ℤ) ≠  0 := by linarith,
have t := q,
rw ← mul_right_inj' r at q,
rw mul_one at q,
rw fac_this a.x a.y at q,
have hb : 0 ≤ (2 * a.x + a.y) ^ 2 := sq_nonneg (2 * a.x + a.y),
have hbb : 7 * a.y ^ 2 ≤  4 := by linarith,
have c : a.y^2 = 0 ∨ a.y^2 > 0 := sq_tauto a.y,
cases c with wc lc,{
have tt : a.y = 0 := pow_eq_zero wc,
rw tt at t,
ring_nf at t,
clear k r q hb hbb wc,
have h := sq_eq_one_iff.mp t,
cases h,
left,
ext,
exact h,
exact tt,
right,
ext,
exact h,
exact tt,
},
exfalso,
linarith,
end

lemma unit_iff_norm_one (a : ℤα) : is_unit a ↔ nat_Norm a = 1 :=
begin
split,
exact unit_if_norm_one a,
intro h,
have p := units_are h,
cases p with ha hb,
use 1,
symmetry,
exact ha,
use -1,
symmetry,
exact hb,
end

--gcd_is_unit_iff is a useful theorem
lemma factors_coprime : is_coprime ((y:ℤα)-α) ((y:ℤα)-α_bar) :=
begin
  sorry,
end

--Main theorem
theorem dioph_eq (x y: ℤ) : 
x^3=y^2-y+2 → (x=2 ∧ y=-2) ∨ (x=2 ∧ y=3) :=
begin
sorry,
end


end mordell
end ℤα


