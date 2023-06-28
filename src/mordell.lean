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
  algebra.ring.divisibility
  data.nat.prime_norm_num
  algebra.gcd_monoid.basic
  algebra.group.units
  algebra.group.defs


open_locale classical

set_option profiler true

namespace ℤα
--variables (a b : ℤα)
-- #check a+b
-- #eval (⟨1,2⟩: ℤα)
-- #print instances  euclidean_domain

section mordell
parameters { x y : ℤ } (sol: x^3 = y^2 - y + 2)

--Note that we have rewritten a.x and a.y for (a : ℤα) to a.z and a.w
--in rt_7_ring, to avoid confusion and potential clashes with x and y here.

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
--#print instances is_domain

noncomputable
def d := euclidean_domain.gcd ((y:ℤα)-α) ((y:ℤα)-α_bar)
/- 
We work towards showing that (y-α) and (y-α_bar) are coprime, i.e.
their gcd (represented by d) is a unit. By considering the difference 
of the two terms, we find that Norm d ∣ 7, and hence N(d) is 1 or 7.
In the case where we assume N(d) = 7, we arrive at a contradiction of the form 
7^2 ∣ y^2-y+2 and ¬(7^2 ∣ y^2-y+2). Hence N(d) = 1 and d is a unit.
-/

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

--Shows that the factorization of y^2-y+2 is valid.
lemma my_factorization: (y:ℤα)^2-y+2 = (y-α)*(y-α_bar):=
  begin
  transitivity (y:ℤα)^2 - (α+α_bar)*y + α*α_bar, {
    congr,
    have r : α + α_bar = one,{
    unfold α,
    unfold α_bar,
    refl,
    },
    rw r,
    have q : one*(y:ℤα)=(y:ℤα) := one_mul (y:ℤα),
    rw q,
  },
  rw right_distrib (α:ℤα) (α_bar) (y),
  rw mul_comm (α_bar:ℤα) (y),
  rw mul_sub_right_distrib (y:ℤα) (α) ((y:ℤα) - α_bar),
  rw mul_sub_left_distrib (y:ℤα) (y) (α_bar),
  rw mul_sub_left_distrib (α:ℤα) (y) (α_bar),
  rw pow_two (y:ℤα),
  rw add_comm ((α:ℤα)*y) (y*α_bar),
  rw ← sub_sub ((y:ℤα)*(y:ℤα)) ((y:ℤα)*α_bar) (α*(y:ℤα) ),
  nth_rewrite 1 ← add_zero ((y:ℤα)*α_bar),
  rw ← sub_sub ((y:ℤα)*(y:ℤα)) ((y:ℤα)*α_bar) (0),
  rw ← neg_zero,
  --rw neg_neg (0:ℤα), 
  --rw ← sub_add ((-(y:ℤα))*α_bar) (α*(y:ℤα)) (α*α_bar),
  --??rw left_distrib (-1:ℤα) (y*α_bar) (α*y),
  show_term{ring_nf},

  end

/- d = gcd (y-α) (y-α_bar) divides the difference of
   (y-α_bar) and (y-α), which is sqrt(7)i. -/
lemma d_dvd_sqrt_seven_i : d ∣ α - α_bar :=
begin
change ∃(k:ℤα), α - α_bar = d*k,
have h : d ∣ y - α := euclidean_domain.gcd_dvd_left (y - α) (y - α_bar),
have q : d ∣ y - α_bar := euclidean_domain.gcd_dvd_right (y - α) (y - α_bar),
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

lemma seven_prime : nat.prime 7 :=
begin
norm_num,
end


lemma nat_nd_one_or_seven : nat_Norm d = 1 ∨ nat_Norm d = 7 :=
begin
exact nat.prime.eq_one_or_self_of_dvd (seven_prime) (nat_Norm d) (nat_nd_dvd_seven),
end

--After arriving at the result below, we then show that N(d)=7 leads to a contradiction.
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
  change (⟨y+0,-1⟩:ℤα) = (⟨y,-1⟩:ℤα),
  rw add_zero,
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
exact euclidean_domain.gcd_dvd_left (y - α) (y - α_bar),
end

--The usual maths definition for y % 7 = s
lemma y_mod_seven (s:ℤ) (h : y % 7 = s) : ∃(k:ℤ), y = 7*k + s :=
begin
have q := int.dvd_sub_of_mod_eq h,
cases q with l lh,
use l,
rw  ← add_right_inj (s:ℤ) at lh,
rw add_comm (s:ℤ) (y-s) at lh,
rw add_comm (s:ℤ) (7*l) at lh,
rw sub_add_cancel at lh,
exact lh,
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
have j : (0:ℤ) < 2 := by dec_trivial,
have g := int.le_of_dvd j h,
have ng : ¬ (7 ≤ 2) := by dec_trivial,

show_term{linarith},
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
-- isn't it best to use ring_nf here?
ring_nf,
},
rw dvd_add_right r at h,
have j : (0:ℤ) < 2 := by dec_trivial,
have g := int.le_of_dvd j h,
show_term{linarith},
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
show_term{linarith},
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

--Now we put the previous lemmas together. (We are assuming N(d)=7.)
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
include sol
lemma stuff_bro (h : Norm d = 7) : 7 ∣ x^3 :=
begin
have p : 7 ∣ y^2 - y + 2, {
  rw ← h,
  exact nd_dvd_pol,
},
rw sol,
exact p,
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
rw ← sol,
apply seven_sq_dvd sol,
apply sev_dvd_x_cubed sol,
apply stuff_bro sol,
exact h,
end

--Shows by contradiction that N(d) must be 1.
lemma nd_eq_one : Norm d = 1 :=
begin
have h := nd_one_or_seven,
cases h with t f,
exact t,
exfalso,
have b := seven_sq_dvd_sol sol f,
exact seven_sq_negdvd_full f b,
end
omit sol

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
change 1 ≤  a.w^2  at lc,
have mt : 7*1 ≤  7*a.w^2,{
  apply mul_le_mul_left' lc,
},
--have nt : ¬ (7 * a.w ^ 2 ≤ 4),
sorry,
--show_term{linarith [hbb, lc]},
end

#check int.
lemma units_is_bruv (a:ℤαˣ) : (a:ℤα) = 1 ∨ (a:ℤα) = -1 :=
begin
have q := units.is_unit a,
have p := unit_if_norm_one a q,
have l := units_are p,
exact l,
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
 exact nd_eq_one sol,
end

lemma descent : ∃(k : ℤα), associated (k^3) ((y:ℤα)-α) :=
begin
have h : ((y:ℤα)-α)*(y-α_bar) = x^3,{
rw ← my_factorization,
symmetry,
norm_cast,
ext,
exact sol,
refl,
},
exact exists_associated_pow_of_mul_eq_pow' (factors_coprime sol) h,
end


lemma descent_pro : ∃(k : ℤα), k^3 = ((y:ℤα)-α) :=
begin
have h := descent sol,
cases h with b hb,
unfold associated at hb,
cases hb with c hc,
have p := units_is_bruv c, 
cases p with p1 p2,{
rw p1 at hc,
rw mul_one at hc,
use b,
exact hc,
},
rw p2 at hc,
use -b,
show_term{simp},
simp at hc,
exact hc,
end
omit sol

lemma alpha_rw (a : ℤ) (b : ℤ) : (a:ℤα) + b*α = (⟨a, b⟩:ℤα) :=
begin
change (⟨a + (b*0 - 2*0*1), 0 + (b*1 + 0*0 + 0*1)⟩:ℤα) = (⟨a, b⟩:ℤα),
simp,
end

include sol

lemma expanding : ∃(k:ℤα), (y:ℤα)-α = k.z^3 - 6*k.z*k.w^2 - 2*k.w^3 + (3*k.z^2*k.w + 3*k.z*k.w^2 - k.w^3)*α :=
begin
have h := descent_pro sol,
cases h with k hk,
use k,
rw ← hk,
have p : k = k.z + k.w*α, {
change k = (⟨k.z + (k.w*0 - 2*0*1), 0 + (k.w*1 + 0*0 + 0*1)⟩:ℤα),
simp,
ext,
simp,
},
nth_rewrite 0 p,
ring_nf,
end

omit sol
lemma neg_coe (a:ℤ) : -(a:ℤα) = (-a:ℤα) := 
begin
simp,
end
include sol

lemma separating : ∃(k:ℤα), y = k.z^3 - 6*k.z*k.w^2 - 2*k.w^3 ∧ -1 = 3*k.z^2*k.w + 3*k.z*k.w^2 - k.w^3 :=
begin
have h := expanding sol,
cases h with k hk,
use k,
nth_rewrite 0 ← one_mul α at hk,
have pp := alpha_rw y (-1),
change (y:ℤα) - 1 * α = (⟨y, -1⟩:ℤα) at pp,
rw pp at hk,
norm_cast at hk,
have ppp := alpha_rw (k.z ^ 3 - 6 * k.z * k.w ^ 2 - 2 * k.w ^ 3) (3 * k.z ^ 2 * k.w + 3 * k.z * k.w ^ 2 - k.w ^ 3),
rw ppp at hk,
clear pp ppp,
simp at hk,
split,
exact hk.1,
exact hk.2,
end

lemma divides_one_trick (k:ℤα) (h : -1 = 3*k.z^2*k.w + 3*k.z*k.w^2 - k.w^3) : k.w = 1 ∨ k.w = -1 :=
begin
have q : (-1:ℤ) ≠ 0 := by linarith,
have p : k.w ∣ 1, {
use -3 * k.z ^ 2 - 3 * k.z * k.w + k.w ^ 2,
rw ← mul_right_inj' q,
ring_nf,
rw h,
ring_nf,
},
have g : (0 ≤ k.w) ∨ (0 ≤ -k.w), 
{
  by_contra,
  rw not_or_distrib at h,
  cases h with f hf,
  apply hf,
  linarith,
},
cases g with t ht,
have q := int.eq_one_of_dvd_one t p,
left,
exact q,
rw ← neg_dvd at p,
have l := int.eq_one_of_dvd_one ht p,
right,
rw ← mul_right_inj' q,
simp,
exact l,
end

omit sol

lemma kw_eq_one (k:ℤα) (h : k.w = 1) (j : -1 = 3 * k.z ^ 2 * k.w + 3 * k.z * k.w ^ 2 - k.w ^ 3) : (k.z = 0 ∨ k.z = -1) :=
begin
rw h at j,
simp at j,
rw ← add_right_inj (1:ℤ) at j,
simp at j,
change 3*0 = 3 * k.z ^ 2 + 3 * k.z at j,
rw ← mul_add 3 (k.z^2) (k.z) at j,
have dumb : (3:ℤ) ≠ 0 := by linarith,
rw mul_right_inj' dumb at j,
have u : (k.z * 1) = k.z := by linarith,
nth_rewrite 1 ← u at j,
have t : k.z^2 = k.z*k.z := by linarith,
rw t at j,
rw ← mul_add k.z k.z 1 at j,
simp at j,
cases j,
left,
exact j,
right,
-- can definitely not use linarith
linarith,
end

include sol
lemma sol_kz_eq_zero (k:ℤα) (h : k.z = 0) (p : k.w = 1) (q : y = k.z^3 - 6*k.z*k.w^2 - 2*k.w^3) : x = 2 ∧ y = -2 :=
begin
rw h at q,
rw p at q,
norm_num at q,
split,{
rw q at sol,
norm_num at sol,
have gg : (8:ℤ) = 2^3 := by norm_num,
rw gg at sol,

have plop : 0 ≤ x ∨ 0 ≤ -x, {
  by_contra,
  rw not_or_distrib at h,
  cases h with f hf,
  apply hf,
  linarith,
},
have bloop : (0:ℤ) ≤ 2 := by linarith,
have gloop : (0:ℕ) < 3:= by linarith,
cases plop,
rwa pow_left_inj plop bloop gloop at sol,
exfalso,
simp at plop,
have snoop : odd 3 := by norm_num,
rw ← odd.pow_nonpos_iff snoop at plop,
rw sol at plop,
linarith,
},
exact q,
end

lemma sol_kz_eq_neg_one (k:ℤα) (h : k.z = -1) (p : k.w = 1) (q : y = k.z^3 - 6*k.z*k.w^2 - 2*k.w^3) : x=2 ∧ y=3 :=
begin
rw h at q,
rw p at q,
norm_num at q,
split,{
rw q at sol,
norm_num at sol,
have gg : (8:ℤ) = 2^3 := by norm_num,
rw gg at sol,

have plop : 0 ≤ x ∨ 0 ≤ -x, {
  by_contra,
  rw not_or_distrib at h,
  cases h with f hf,
  apply hf,
  linarith,
},
have bloop : (0:ℤ) ≤ 2 := by linarith,
have gloop : (0:ℕ) < 3:= by linarith,
cases plop,
rwa pow_left_inj plop bloop gloop at sol,
exfalso,
simp at plop,
have snoop : odd 3 := by norm_num,
rw ← odd.pow_nonpos_iff snoop at plop,
rw sol at plop,
linarith,
},
exact q,
end


lemma kw_eq_neg_one (k:ℤα) (h : k.w = -1) (j : -1 = 3 * k.z ^ 2 * k.w + 3 * k.z * k.w ^ 2 - k.w ^ 3) : false :=
begin
rw h at j,
rw ← add_left_inj (1:ℤ) at j,
ring_nf at j,
have dumb : (-1:ℤ) ≠ 0 := by linarith,
rw ← mul_right_inj' dumb at j,
ring_nf at j,

have c : (k.z ≤ -1 ∨ k.z = 0 ∨ k.z = 1 ∨ k.z ≥ 2),{
by_contra p,
rw not_or_distrib at p,
rw not_or_distrib at p,
rw not_or_distrib at p,
cases p with p1 g1,
cases g1 with p2 g2,
cases g2 with p3 p4,
nlinarith,
},

cases c,{
nlinarith,
},
cases c,{
rw c at j,
linarith,
},
cases c,{
rw c at j,
linarith,
},
nlinarith,
end


theorem diophantine_eq : (x = 2 ∧ y = -2) ∨ (x = 2 ∧ y = 3) :=
begin
have h := separating sol,
cases h with k hk,
cases hk with a b,
have p := divides_one_trick sol k b,
cases p with p1 p2,
have bam := kw_eq_one k p1 b,
cases bam,
left,
exact sol_kz_eq_zero sol k bam p1 a,
right,
exact sol_kz_eq_neg_one sol k bam p1 a,
exfalso,
exact kw_eq_neg_one sol k p2 b,
end
omit sol

end mordell
end ℤα


