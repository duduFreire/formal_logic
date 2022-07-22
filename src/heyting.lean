import tactic
import order.zorn

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

noncomputable def infimum_of_finite (A : set X) (A_fin : set.finite A) :=
 classical.some (has_infimum_of_finite A_fin)

def infimum_of_finite_spec (A : set X) (A_fin : set.finite A) := 
 classical.some_spec (has_infimum_of_finite A_fin)

lemma infimum_iff {A : set X} (A_fin : set.finite A) (s : X) : 
infimum A s ↔ s = infimum_of_finite A A_fin :=
begin 
	split,
	{
		intro h,
		have h_inf : infimum A (infimum_of_finite A A_fin) := infimum_of_finite_spec A A_fin,
		exact ge_antisymm (h.2 h_inf.1) (h_inf.2 h.1),
	},
	{
		intro h,
		rw h,
		exact infimum_of_finite_spec A A_fin,
	}
end

variables {H : Type u} [heyting H]
structure filter (F : set H) : Prop :=
(mem_inter : ∀ {a b}, a ∈ F → b ∈ F → a ∩ b ∈ F)
(mem_ge : ∀ {a b}, a ∈ F → a ≤ b → b ∈ F)

structure prime_filter (F : set H) extends filter F : Prop :=
(mem_union : ∀ {a b}, a ∪ b ∈ F → a ∈ F ∨ b ∈ F)

lemma smallest_filter_insert {F : set H} (F_filter : filter F) 
(F_nonempty : F.nonempty) (b : H)  : 
let F' := {a : H | ∃c : H, c ∈ F ∧ b ∩ c ≤ a} in
filter F' ∧ F ∪ {b} ⊆ F' ∧ ∀ {G : set H}, filter G → F ∪ {b} ⊆ G → F' ⊆ G :=
begin 
	split, fconstructor,
	{
		intros x y hx hy,
		simp at *,
		rcases hx with ⟨c, hc, hcx⟩,
		rcases hy with ⟨d, hd, hdy⟩,
		use [c ∩ d, F_filter.mem_inter hc hd],
		split,
		{ rw heyting.min_assoc, exact le_min_of_le d hcx },
		{
			rw [heyting.min_assoc, heyting.min_comm b c,
			 ←heyting.min_assoc, heyting.min_comm],
			 exact le_min_of_le c hdy,
		},
	},
	{
		intros x y hx hxy,
		simp at *,
		rcases hx with ⟨c, hc, hcx⟩,
		use [c, hc, le_trans hcx hxy],
	}, split,
	{
		intros x hx,
		simp at *,
		cases hx,
		{
			use ⊤, split,
			{
				cases set.nonempty_def.mp F_nonempty with f hf,
				apply F_filter.mem_ge hf,
				rw← le_iff,
				simp,
			},
			{ rw hx, simp }
		},
		{
			use [x, hx], 
			exact min_le_self_right b x,
		},
	},
	{
		intros G G_filter G_sup x hx,
		simp at hx,
		rcases hx with ⟨c, hc, hcx⟩,
		have hcG : c ∈ G := G_sup (or.inl hc),
		have hbG : b ∈ G := by {apply G_sup, simp},
		exact G_filter.mem_ge (G_filter.mem_inter hbG hcG) hcx,
	}
end

lemma exists_big_prime_filter {F : set H} (F_filter : filter F)
(F_nonempty : F.nonempty) {a : H} (haF : a ∉ F) :
∃ (M : set H), prime_filter M ∧ F ⊆ M ∧ a ∉ M :=
begin 
	set A := {G : set H | filter G ∧ a ∉ G} with A_def,
	have hFA : F ∈ A := by { rw A_def, simp, exact ⟨F_filter, haF⟩ },
	rcases zorn_subset_nonempty A _ F hFA with ⟨M, hMA, F_sub, M_max⟩,
	{
		use M,
		have M_filter : filter M := by { rw A_def at hMA, simp at hMA, exact hMA.1 },
		have hMa : a ∉ M := by { rw A_def at hMA, simp at hMA, exact hMA.2 },
		have M_nonempty : M.nonempty := set.nonempty.mono F_sub F_nonempty,
		refine ⟨_, F_sub, hMa⟩,
		fconstructor, { exact M_filter },

		have wlog : ∀ {b c}, b ∪ c ∈ M → b ∉ M → c ∉ M → b ≠ a → false,
		{
			intros b c hcup hb hc hba,
			rcases smallest_filter_insert M_filter M_nonempty b 
			with ⟨G_filter, G_sup, G_small⟩,
			by_cases haG : a ∈ {a : H | ∃ (c : H), c ∈ M ∧ b ∩ c ≤ a},
			{
				simp at haG,
				rcases haG with ⟨d, hd, hda⟩,
				
				sorry,
			},
			{
				have hGA : {a : H | ∃ (c : H), c ∈ M ∧ b ∩ c ≤ a} ∈ A,
				{
					rw A_def, 
					simp only [set.mem_set_of_eq],
					use G_filter,
				},
				have M_ss_G : M ⊆ {a : H | ∃ (c : H), c ∈ M ∧ b ∩ c ≤ a} :=
				λ x hx, G_sup (or.inl hx),
				specialize M_max _ hGA M_ss_G,
				rw M_max at *,
				exact hb (G_sup (by finish)),
			},
		},

		by_contradiction,
		push_neg at h,
		rcases h with ⟨b, c, hcup, hb, hc⟩,
		have hb_or_c_neq_a : b ≠ a ∨ c ≠ a,
		{
			by_contradiction contra,
			push_neg at contra,
			rw [contra.1, contra.2] at hcup,
			simp at hcup,
			rw A_def at hMA, simp at hMA,
			exact hMA.2 hcup,
		},

		cases hb_or_c_neq_a,
		{ exact wlog hcup hb hc hb_or_c_neq_a },
		{ rw heyting.max_comm at hcup, exact wlog hcup hc hb hb_or_c_neq_a },
	},
	sorry,
end


end heyting