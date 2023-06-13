import
  tactic
  data.complex.basic
  ring_theory.euclidean_domain
  .rt_7_ring
  ring_theory.coprime.basic
  ring_theory.principal_ideal_domain
  number_theory.divisors
  algebra.group.units
  

namespace ℤα
variables (a b : ℤα)
#check a+b
#eval (⟨1,2⟩: ℤα)
#print instances  euclidean_domain

open complex

open euclidean_domain

section mordell
parameters { x y : ℤ } {sol : x^3 = y^2 - y + 2}

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

lemma sev_dvd_x_cubed (h : 7 ∣ x^3) : 7 ∣ x :=
begin
sorry,
end

-- find mathlib lemma for y % 7 = 4 → ∃k, y = 7k+4
-- use interval_cases and the above lemmas
lemma seven_dvd_pol (h : 7 ∣ y^2 - y + 2) : y % 7 = 4 :=
begin
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

lemma units_are {a:ℤα} (h : is_unit a): a = 1 ∨ a = -1 := 
begin
have k := unit_if_norm_one a h,
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
clear h k r q hb hbb wc,
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


