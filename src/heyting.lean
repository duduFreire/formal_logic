import tactic

namespace heyting

universe u

class has_imp (X : Type u) := (imp : X -> X -> X)

infix ` => `:50 := has_imp.imp

class heyting (X : Type u) extends has_inter X, has_union X, has_imp X,
has_bot X, has_top X :=
(max_assoc : ∀a b c : X, a ∪ (b ∪ c) = (a ∪ b) ∪ c)
(min_assoc : ∀a b c : X, a ∩ (b ∩ c) = (a ∩ b) ∩ c)
(max_comm : ∀a b : X, a ∪ b = b ∪ a)
(min_comm : ∀a b : X, a ∩ b = b ∩ a)
(min_dist : ∀a b c : X, a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c))
(max_dist : ∀a b c : X, a ∪ (b ∩ c) = (a ∪ b) ∩ (a ∪ c))
(max_id : ∀a : X, a ∪ ⊥ = a)
(min_id : ∀a : X, a ∩ ⊤ = a)
(max_self : ∀a : X, a ∪ a = a)
(imp_ge : ∀a b c : X, (a ∩ c) ∪ b = b ↔ c ∪ (a => b) = (a => b))

variables {X : Type u} [heyting X] (a b c x y : X)

@[simp]lemma max_bot : a ∪ ⊥ = a := heyting.max_id a
@[simp]lemma bot_max : ⊥ ∪ a = a := by {rw _inst_1.max_comm, exact max_bot a}
@[simp]lemma min_top : a ∩ ⊤ = a := heyting.min_id a
@[simp]lemma top_min : ⊤ ∩ a = a := by {rw _inst_1.min_comm, exact min_top a}
@[simp]lemma max_self : a ∪ a = a := heyting.max_self a

instance heyting_le : has_le X := ⟨λa b, a ∪ b = b⟩

lemma le_iff : a ∪ b = b ↔ a ≤ b := iff.refl (a ∪ b = b)

instance heyting_partial : partial_order X := 
{
  le := has_le.le,
  le_refl := begin 
    unfold has_le.le,
    simp,
  end,
  le_trans := begin 
    unfold has_le.le,
    intros a b c hab hbc,
    rw [←hbc, _inst_1.max_assoc, hab],
  end,
  le_antisymm := begin 
    unfold has_le.le,
    unfold preorder.le,
    unfold has_le.le,
    intros a b hab hba,
    rw [←hab], rw _inst_1.max_comm at hba,
    exact eq.symm hba,
  end
}

@[simp]lemma min_bot : a ∩ ⊥ = ⊥ :=
begin 
	have := _inst_1.imp_ge,
	specialize this a ⊥ ⊥,
	simp at this,
	exact this,
end

@[simp]lemma bot_min : ⊥ ∩ a = ⊥ := by {rw _inst_1.min_comm, simp}

@[simp]lemma min_self : a ∩ a = a :=
begin 
	suffices : ((a ∪ ⊥) ∩ a) ∪ ((a ∪ ⊥) ∩ ⊥) = a ∪ (⊥ ∩ ⊥),
	{ simp at *, exact this },
	rw [←_inst_1.min_dist, ←_inst_1.max_dist],
end

lemma le_max_self_left : a ≤ a ∪ b :=
begin 
  rw← le_iff,
  rw _inst_1.max_assoc,
  simp,
end

lemma le_max_self_right : b ≤ a ∪ b :=
begin 
  rw← le_iff,
  rw _inst_1.max_comm,
  rw← _inst_1.max_assoc,
  simp,
end

lemma min_le_self_left : a ∩ b ≤ a :=
begin
	rw ← le_iff,
	suffices : a ∪ ((a ∩ ⊥) ∪ (a ∩ b)) = a ∪ (⊥ ∩ b),
	{ simp at this,rwa _inst_1.max_comm at this },
	suffices : ((a ∪ ⊥) ∩ a) ∪ ((a ∪ ⊥) ∩ b) = a ∪ (⊥ ∩ b),
	{simp at *, exact this},
	rw← _inst_1.min_dist,
	rw _inst_1.max_dist,
end

lemma min_le_self_right : a ∩ b ≤ b :=
begin
	rw _inst_1.min_comm,
	exact min_le_self_left b a,
end

lemma le_min_of_le {a c} : a ≤ c → a ∩ b ≤ c := λh, le_trans (min_le_self_left a b) h

@[simp]lemma max_le_iff : a ∪ b ≤ c ↔ a ≤ c ∧ b ≤ c := 
begin 
	--rw [←le_iff,←le_iff,←le_iff],
	split,
	{
		intro h,
		have h1 := le_max_self_left a b,
		have h2 := le_max_self_right a b,
		exact ⟨le_trans h1 h, le_trans h2 h⟩,
	},
	{
    intro h,
    cases h with h1 h2,
    rw← le_iff at *,
		rw← _inst_1.max_assoc,
		rwa h2,
	},
end

@[simp]lemma le_min_iff : a ≤ b ∩ c ↔ a ≤ b ∧ a ≤ c :=
begin 
  split,
  {
    intro h,
		have h1 := min_le_self_left b c,
		have h2 := min_le_self_right b c,
		exact ⟨le_trans h h1, le_trans h h2⟩,
  },
  {
    intro h,
    cases h with h1 h2,
    rw← le_iff at *,
    rw _inst_1.max_dist,
    rw h1, rw h2,
  }
end

@[simp]lemma max_top : a ∪ ⊤ = ⊤ :=
begin 
	have := min_le_self_left ⊤ a,
	rw← le_iff at this,
	simp at this,
	exact this,
end

@[simp]lemma top_max : ⊤ ∪ a = ⊤ :=
begin 
	rw _inst_1.max_comm,
	exact max_top a,
end

def upper_bound (A : set X) (x : X) := ∀{a}, a ∈ A → a ≤ x 
def lower_bound (A : set X) (x : X) := ∀{a}, a ∈ A → x ≤ a 
def supremum (A : set X) (x : X) := upper_bound A x ∧ ∀{s}, upper_bound A s → x ≤ s
def infimum (A : set X) (x : X) := lower_bound A x ∧ ∀{s}, lower_bound A s → s ≤ x

lemma infimum_empty : infimum (∅ : set X) ⊤ :=
begin 
	split,
	{ intros x hx, exfalso, exact set.not_mem_empty x hx },
	{
		intros s' hs',
		rw← heyting.le_iff,
		simp,
	}
end

lemma infimum_insert {B : set X} {a t : X} (ht : infimum B t) : infimum (insert a B) (t ∩ a) :=
begin 
	split,
	{
	intros x hx,
	simp at *,
	cases hx,
	{
		rw hx,
		exact min_le_self_right t a,
	},
	{
		cases ht with ht1 ht2,
		have h1 := ht1 hx,
		exact le_min_of_le a (ht1 hx),
	},
	},
	{
	intros s' hs',
	simp,
	have : lower_bound B s',
	{
		intros y hy,
		exact hs' (set.mem_insert_of_mem a hy),
	},
		exact ⟨ht.2 (by assumption), hs' (set.mem_insert a B)⟩,
	}
end

lemma has_infimum_of_finite {A : set X} (A_fin : set.finite A) : ∃ s, infimum A s :=
begin 
	refine set.finite.induction_on A_fin ⟨⊤, infimum_empty⟩ _,
	{
		intros a B has B_fin ih,
		rcases ih with ⟨t, ht⟩,
		use t ∩ a,
		exact infimum_insert ht,
	}
end

instance min_comm_inst : 
@is_commutative X (heyting.to_has_inter).inter := ⟨λ a b, heyting.min_comm a b⟩ 

instance min_assoc_inst : 
@is_associative X (heyting.to_has_inter).inter := ⟨λ a b c, eq.symm (heyting.min_assoc a b c)⟩ 

-- def awaeawe {A : set X}  (A_fin : set.finite A) : Prop :=
-- begin 
-- 	have := A_fin.to_finset.val,
-- end

-- def testaa  {A : set X} : A.finite → X := λ A_fin,
-- @multiset.fold X (@has_inter.inter X (heyting.to_has_inter))
-- 	 (@heyting.min_comm_inst X _inst_1) (@heyting.min_assoc_inst X _inst_1) ⊤ A_fin.to_finset.val

noncomputable def infimum_of_finite {A : set X} (A_fin : set.finite A) :=
 classical.some (has_infimum_of_finite A_fin)

def infimum_of_finite_spec {A : set X} (A_fin : set.finite A) := 
 classical.some_spec (has_infimum_of_finite A_fin)

lemma infimum_iff {A : set X} (A_fin : set.finite A) (s : X) : 
infimum A s ↔ s = infimum_of_finite A_fin :=
begin 
	split,
	{
		intro h,
		have h_inf : infimum A (infimum_of_finite A_fin) := infimum_of_finite_spec A_fin,
		exact ge_antisymm (h.2 h_inf.1) (h_inf.2 h.1),
	},
	{
		intro h,
		rw h,
		exact infimum_of_finite_spec A_fin,
	}
end

end heyting