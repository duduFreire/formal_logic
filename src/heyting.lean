import tactic

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

@[simp]lemma union_id : a ∪ ⊥ = a := heyting.max_id a
@[simp]lemma inter_id : a ∩ ⊤ = a := heyting.min_id a
@[simp]lemma union_self : a ∪ a = a := heyting.max_self a

instance heyting_le : has_le X := ⟨λa b, a ∪ b = b⟩

@[simp]lemma le_iff : a ∪ b = b ↔ a ≤ b := iff.refl (a ∪ b = b)

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

@[simp]lemma inter_self : a ∩ a = a :=
begin 
  sorry
end

lemma le_max_self_left : a ≤ a ∪ b :=
begin 
  rw← le_iff,
  rw _inst_1.max_assoc,
  simp,
end

lemma le_max_self_right : a ≤ b ∪ a :=
begin 
  rw← le_iff,
  rw _inst_1.max_comm,
  rw← _inst_1.max_assoc,
  simp,
end

lemma min_le_self_left : a ∩ b ≤ a :=
begin 
  rw← le_iff,
  rw _inst_1.max_comm,
  rw _inst_1.max_dist,
  sorry,
end

lemma union_top : a ∪ ⊤ = ⊤ := sorry

lemma le_min_of_le : a ≤ c → a ∩ b ≤ c :=
begin 
  intro h,
  rw← le_iff at *,
  rw _inst_1.max_comm,
  rw _inst_1.max_dist,
  rw _inst_1.max_comm at h,
  rw h,
  sorry,
end

@[simp]lemma le_inter_iff : a ≤ b ∩ c ↔ a ≤ b ∧ a ≤ c :=
begin 
  split,
  {
    intro h,
    sorry,
  },
  {
    intro h,
    cases h with h1 h2,
    rw← le_iff at *,
    rw _inst_1.max_dist,
    rw h1, rw h2,
  }
end