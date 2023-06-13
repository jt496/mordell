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

open euclidean_domain

section mordell
parameters { x y : ℤ } {sol: x^3 = y^2 - y + 2}

--Note that we have rewritten a.x and a.y for (a : ℤα) to a.z and a.w
--in rt_7_ring, to avoid confusion and potential clashes with x and y here.

instance : is_principal_ideal_ring ℤα := infer_instance
#print instances is_principal_ideal_ring
#print instances normalized_gcd_monoid

noncomputable
def d := euclidean_domain.gcd ((y:ℤα)-α) ((y:ℤα)-α_bar)
/- 
We work towards showing that (y-α) and (y-α_bar) are coprime, i.e.
their gcd (represented by d) is a unit. By considering the difference 
of the two terms, we find that Norm d ∣ 7, and hence N(d) is 1 or 7.
In the case where we assume N(d) = 7, we arrive at a contradiction of the form 
7^2 ∣ y^2-y+2 and ¬(7^2 ∣ y^2-y+2). Hence N(d) = 1 and d is a unit.
-/

-- Showing that conj complex_α is in fact α_bar. Not in use currently.
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

  --Key lemma
  lemma norm_divides (a p : ℤα):
  (p ∣ a) → (Norm p ∣ Norm a):=
  begin
  intro h,
  cases h with n hn,
  use Norm n,
  rw ← Norm_mul p n,
  rw hn,
  end

-- don't know how to prove this, maybe we will need a proper coercion?
lemma coe_from_ints (a:ℤ) : (a:ℤα) = (⟨a, 0⟩:ℤα) :=
begin
unfold_coes,

sorry,
end

--Shows that the factorization of y^2-y+2 is valid.
lemma my_factorization: (y:ℤα)^2-y+2 = (y-α)*(y-α_bar):=
  begin
  transitivity (y:ℤα)^2 - (α+α_bar)*y + α*α_bar, {
    congr,
    have r : α + α_bar = one := by ring_nf,
    rw r,
    have q : one*(y:ℤα)=(y:ℤα) := one_mul (y:ℤα),
    rw q,
  },
  ring_nf,
  end

/- d = gcd (y-α) (y-α_bar) divides the difference of
   (y-α_bar) and (y-α), which is sqrt(7)i. -/
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

--Applying norm_divides to d_dvd_sqrt_seven_i
lemma nd_dvd_seven : Norm d ∣ 7 :=
begin
have h := d_dvd_sqrt_seven_i,
--Why is it showing an extra goal?
have q := norm_divides (α - α_bar) d h,
rw norm_seven at q,
exact q,
end

lemma nat_nd_dvd_seven : nat_Norm d ∣ 7 :=
begin
have h := nd_dvd_seven,
--new lemma added to rt_7_ring, equiv_norms
rw equiv_norms at h,
exact_mod_cast h,
end

--There's definitely an easy way to do this...
lemma seven_prime : nat.prime 7 :=
begin
sorry,
end


lemma nat_nd_one_or_seven : nat_Norm d = 1 ∨ nat_Norm d = 7 :=
begin
exact nat.prime.eq_one_or_self_of_dvd (seven_prime) (nat_Norm d) (nat_nd_dvd_seven),
end

--After arriving at this result, we now show that N(d)=7 leads to a contradiction.
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
change add (⟨y, 0⟩:ℤα) (⟨0, 1⟩:ℤα).neg = {z := y, w := -1},
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

/- Using the fact that d divides y-α, we see that N(d) divides N(y-α).
Later we will assume that N(d) = 7 to get 7 ∣ y^2 - y + 2 (using the lemma below), 
and solve this case by case to find that y % 7 = 4. This will aid us in setting up
the contradiction.
-/
lemma nd_dvd_pol : Norm d ∣ y^2 - y + 2 :=
begin
rw ← norm_y_minus_α,
apply norm_divides,
exact gcd_dvd_left (y - α) (y - α_bar),
end

--The usual maths definition for y % 7 = s
lemma y_mod_seven (s:ℤ) (h : y % 7 = s) : ∃(k:ℤ), y = 7*k + s :=
begin
have q := int.dvd_sub_of_mod_eq h,
cases q with l lh,
use l,
linarith,
end 

--The following lemmas show case by case that only y such that y % 7 = 4
--solves 7 ∣ y^2 - y + 2. Namely y % 7 = 0, 1, 2, 3, 5, or 6 fail.
------------------------------------------------
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

--------------------------------------------

--Putting the previous lemmas together, we are now assuming N(d)=7.
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

exfalso,
exact y_eq_zero_mod_seven h h_1,
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

--Using the result of the last lemma, we show that ¬(7^2 ∣ y^2 - y + 2).
lemma seven_sq_negdvd (h : y % 7 = 4) (p : 7^2 ∣ y^2 - y + 2) : false :=
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

--Finally we tie this back to our assumption that N(d) = 7.
lemma seven_sq_negdvd_full (h : Norm d = 7) (p : 7^2 ∣ y^2 - y + 2) : false:=
begin
have q := seven_dvd_pol h,
exact seven_sq_negdvd q p,
end

--Now we start working towards the other side of the contradiction.
lemma stuff_bro (h : Norm d = 7) : 7 ∣ x^3 :=
begin
have p : 7 ∣ y^2 - y + 2, {
  rw ← h,
  exact nd_dvd_pol,
},
--This should be a direct application of sol, but Include sol causes problems.
sorry,
-- rw sol,
-- exact h,
end

--Since 7 is prime, it must also divide x.
lemma sev_dvd_x_cubed (h : 7 ∣ x^3) : 7 ∣ x :=
begin
have p := int.prime.dvd_pow' (seven_prime) (h),
exact_mod_cast p,
end

--It follows that 7^3 ∣ x^3, and then that 7^2 ∣ x^3.
lemma seven_sq_dvd (h : 7 ∣ x) : (7^2 ∣ x^3) :=
begin
have p := pow_dvd_pow_of_dvd h 3,
cases p with f hf,
use 7*f,
linarith,
end

--Finally we use that x^3 = y^2 - y + 2 and tie this result back to
--our assumption that N(d) = 7. We have the other side of the contradiction.
lemma seven_sq_dvd_sol (h : Norm d = 7) : (7^2 ∣ y^2 - y + 2) :=
begin
--The below code works if we replace y^2 - y + 2 by x^3 in the goal,
--so we just need to get sol working. Then we will be able to rw ← sol
--and go from there.
sorry,
-- apply seven_sq_dvd,
-- apply sev_dvd_x_cubed,
-- apply stuff_bro,
-- exact h,
-- exact y,
end

--Shows by contradiction that N(d) must be 1.
lemma nd_eq_one : Norm d = 1 :=
begin
have h := nd_one_or_seven,
cases h with t f,
exact t,
exfalso,
have b := seven_sq_dvd_sol f,
exact seven_sq_negdvd_full f b,
end

--If 'a' is a unit it must have norm 1
lemma unit_if_norm_one (a : ℤα) : is_unit a → nat_Norm a = 1 :=
begin
intro h,
rw is_unit_iff_exists_inv at h,
--seems unnecessary to use tauto but we need to get our hypothesis
--into the right form to rewrite it using divides notation.
have p : ∃ (b : ℤα), 1 = a * b := by tauto,
change a ∣ 1 at p,
--applying norm_divides and using the fact that only 1 divides 1 in ℕ.
have l := nat_norm_divides 1 a p,
have d : nat_Norm 1 = 1 := by ring,
rw d at l,
rwa nat.dvd_one at l,
end

--useful factorization of four times the norm, (multiplying by four keeps us in ℤ)
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

--Finding the units of ℤα
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
rw fac_this a.z a.w at q,
--We show first that a.w must be 0.
have hb : 0 ≤ (2 * a.z + a.w) ^ 2 := sq_nonneg (2 * a.z + a.w),
have hbb : 7 * a.w ^ 2 ≤  4 := by linarith,
have c : a.w^2 = 0 ∨ a.w^2 > 0 := sq_tauto a.w,
cases c with wc lc,{
have tt : a.w = 0 := pow_eq_zero wc,
rw tt at t,
ring_nf at t,
clear k r q hb hbb wc,
have h := sq_eq_one_iff.mp t,
--Essentially done, just clean up
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
--hbb and lc cause a contradiction
linarith,
end

--Since we now now what the units are,
--we can write the iff version of the if proof above.
--We also switch from nat_Norm to norm.
lemma unit_iff_norm_one (a : ℤα) : is_unit a ↔ Norm a = 1 :=
begin
split,
intro h,
have l := unit_if_norm_one a h,
rw equiv_norms,
exact_mod_cast l,
intro h,
have j : nat_Norm a = 1,{
  rw equiv_norms at h,
  exact_mod_cast h,
},
have p := units_are j,
cases p with ha hb,
use 1,
symmetry,
exact ha,
use -1,
symmetry,
exact hb,
end

--Finally we can conclude that since N(d)=1, d must be a unit,
--and hence the factors are coprime.
include sol
lemma factors_coprime : is_coprime ((y:ℤα)-α) ((y:ℤα)-α_bar) :=
begin
 rw ← euclidean_domain.gcd_is_unit_iff,
 rw unit_iff_norm_one,
 have k : d = gcd ((y:ℤα)-α) ((y:ℤα)-α_bar) := by refl,
 rw ← k,
 --why does this not work, they are exactly the same???
 exact nd_eq_one,
sorry,
end

--Attempting to start the next step, using the descent lemma from
--mathlib, but we ran into issues. I think we need to get the parameters
--and sol working first.
lemma descent : ∃(k : ℤα), associated ((y:ℤα)-α) (k^3) :=
begin
have h : ((y:ℤα)-α)*(y-α_bar) = x^3,{
rw ← my_factorization,
sorry,
},
--exact exists_associated_pow_of_mul_eq_pow' factors_coprime h,
sorry, 
end


end mordell
end ℤα


