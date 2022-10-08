import tactic

inductive pre_term
| var : ℕ → pre_term 
| app : pre_term → pre_term → pre_term
| abs : ℕ → pre_term → pre_term

def free_variables : pre_term → set ℕ
| (pre_term.var n) := {n}
|	(pre_term.app M N) := free_variables M ∪ free_variables N
| (pre_term.abs n M) := free_variables M \ {n}

lemma free_variables_finite : ∀ M, (free_variables M).finite :=
λ M, pre_term.rec (λ n, set.finite_singleton n)
  (λ M N ihM ihN, ihM.union ihN)
  (λ n M ihn, ihn.diff {n}) M

lemma exists_new_free_var (M N : pre_term) : ∃n, n ∉ free_variables M ∧ n ∉ free_variables N :=
begin 
	 suffices : ∃n, n ∉ (free_variables M ∪ free_variables N),
	 {
		 cases this with n hn,
		 use n,
		 exact not_or_distrib.mp hn,
	 },

	 have : free_variables M ∪ free_variables N ≠ set.univ,
	 {
		intro h,
	 	have h_fin := (free_variables_finite M).union(free_variables_finite N),
		rw h at h_fin,
		exact @not_fintype ℕ nat.infinite (set.fintype_of_finite_univ h_fin),
	 },

	by_contra,
	push_neg at h, apply this,
	ext, split, 
	{ exact λ hx, set.mem_univ x },
	{exact λ gbg, h x},
end


open classical
local attribute [instance] prop_decidable

def closed : pre_term → Prop := λM, free_variables M = ∅

-- noncomputable def subst : pre_term → ℕ → pre_term → pre_term
-- | (pre_term.var n) x N := if x = n then N else pre_term.var n 
-- | (pre_term.app P Q) x N := pre_term.app (subst P x N) (subst Q x N)
-- | (pre_term.abs y P) x N := if x = y then (pre_term.abs y P) else 
-- (
-- 	if x ∈ free_variables P ∧ x ∈ free_variables N then 
-- 	let z := classical.some (exists_new_free_var P N) in let temp := (subst P y (pre_term.var z)) in
-- 	pre_term.abs z (subst temp x N)
-- )

constant subst : pre_term → ℕ → pre_term → pre_term

inductive α_equiv : pre_term → pre_term → Prop
| refl (M) : α_equiv M M
| symm (M N) : α_equiv M N → α_equiv N M 
| trans (M N O) : α_equiv M N → α_equiv N O → α_equiv M O
| app (M M' N N') : α_equiv M M' → α_equiv N N' → α_equiv (pre_term.app M N) (pre_term.app M' N')
| abs (P P' x) : α_equiv P P' → α_equiv (pre_term.abs x P) (pre_term.abs x P')
| rename (P) (x y) :
 y ∉ free_variables P → α_equiv (pre_term.abs x P) (pre_term.abs y (subst P x (pre_term.var y)))

instance lambda_term.setoid : setoid pre_term := 
setoid.mk α_equiv ⟨α_equiv.refl, α_equiv.symm, α_equiv.trans⟩

def lamba_term := quotient lambda_term.setoid 

