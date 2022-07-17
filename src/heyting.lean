import tactic

namespace heyting

universe u

class has_imp (X : Type u) := (imp : X -> X -> X)

infix ` => `:50 := has_imp.imp

class heyting (X : Type u) extends has_inter X, has_union X, has_imp X,
has_bot X, has_top X :=
(max_assoc : ∀a b c : X, a ∪ (b ∪ c) = (a ∪ b) ∪ c)
(min_assoc : ∀a b c : X, a ∩ (b ∩ c) = (a ∩ b) ∪ c)
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

lemma le_min_of_le : a ≤ c → a ∩ b ≤ c := λh, le_trans (min_le_self_left a b) h

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

end heyting