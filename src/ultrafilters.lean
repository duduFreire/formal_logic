import tactic
import tukey

open function set

namespace ultrafilter


@[ext]structure filter (α : Type*) :=
(sets : set (set α))
(univ_sets : univ ∈ sets)
(sets_of_superset {A B} : (A ∈ sets) → (A ⊆ B) → B ∈ sets)
(inter_sets {A B} : A ∈ sets → B ∈ sets → A ∩ B ∈ sets)

variable {α : Type*}

instance : has_mem (set α) (filter α) := ⟨λ A F, A ∈ F.sets⟩
instance : has_le (filter α) := ⟨λ F G, F.sets ⊆ G.sets⟩
instance : partial_order (filter α) := 
{
	le := has_le.le,
	le_refl := λ (a : filter α), rfl.subset,
	le_trans := λ a b c hab hbc, subset.trans hab hbc,
	le_antisymm := 
	begin 
		intros a b hab hba,
		ext,
		exact {mp := @hab x, mpr := @hba x},
	end
}

lemma filter_le_iff (F G : filter α) : F ≤ G ↔ F.sets ⊆ G.sets := iff.refl _

@[simp] lemma mem_filter_iff (x) (F : filter α) : x ∈ F.sets ↔ x ∈ F := iff.refl _

lemma filter_eq (f g : filter α) : f.sets = g.sets ↔ f = g :=
(filter.ext_iff f g).symm

lemma fin_inter_sets {F : filter α} {C : set (set α)} (C_ss : C ⊆ F.sets) (C_fin : C.finite) :
⋂₀ C ∈ F :=
begin 
	suffices : ∀(C_ss : C ⊆ F.sets), ⋂₀ C ∈ F,
	{ exact this C_ss },
	apply set.finite.induction_on C_fin,
	{
		simp,
		exact F.univ_sets,
	},
	{
		intros a s has s_fin hs has,
		have : ⋂₀ insert a s = a ∩ ⋂₀ s := by finish,
		rw this, clear this,
		have haF : a ∈ F := has (mem_insert a s),
		specialize hs (λ x hx, has (mem_insert_of_mem _ hx)),
		exact F.inter_sets haF hs,
	}
end

def fip (A : set (set α)) : Prop := ∀ ⦃B⦄, B ⊆ A → B.finite → ⋂₀ B ≠ ∅

lemma fip_of_subset_fip {A B : set (set α)} (hAB : A ⊆ B) (B_fip : fip B) : fip A :=
λ C hCA C_fin, B_fip (subset.trans hCA hAB) C_fin

def proper_filter (F : filter α) : Prop := ∅ ∉ F

lemma proper_iff_not_univ (F : filter α) : proper_filter F ↔ F.sets ≠ univ :=
begin 
	split,
	{
		intros h contra,
		apply h,
		unfold has_mem.mem, rw contra,
		exact trivial,
	},
	{
		intros h contra,
		apply h,
		ext x, split, intro h, exact trivial,
		intro _, 
		exact F.sets_of_superset contra (empty_subset x),
	}
end

lemma fip_iff_proper_filter (F : filter α) : fip F.sets ↔ proper_filter F :=
begin 
	split; intro h,
	{
		intro contra,
		have : {∅} ⊆ F.sets := by rwa singleton_subset_iff,
		apply h this (finite_singleton ∅),
		rw sInter_singleton,
	},
	{
		intros A A_ss A_fin contra,
		have := fin_inter_sets A_ss A_fin,
		rw contra at this,
		exact h this,
	},
end

def filter_containing (A : set (set α)) : filter α :=
{
	sets := {B : set α | ∃(C) (C_ss : C ⊆ A) (C_fin : C.finite), ⋂₀ C ⊆ B},
	univ_sets := begin 
		simp,
		use [∅, empty_subset A, finite_empty],
	end,
	sets_of_superset := begin 
		simp,
		intros B₁ B₂ C C_ss C_fin interC_ss B_ss,
		use [C, C_ss, C_fin, subset.trans interC_ss B_ss],
	end,
	inter_sets := 
	begin 
		intros A₁ A₂ hA₁ hA₂,
		simp at *,

		rcases hA₁ with ⟨C₁, C₁_ss, C₁_fin, hC₁⟩,
		rcases hA₂ with ⟨C₂, C₂_ss, C₂_fin, hC₂⟩,
		use [C₁ ∪ C₂, union_subset C₁_ss C₂_ss, finite.union C₁_fin C₂_fin],
		split,
		{
			intros x hx,
			apply hC₁,
			intros t ht,
			apply hx,
			exact or.inl ht,
		},
		{
			intros x hx,
			apply hC₂,
			intros t ht,
			apply hx,
			exact or.inr ht,
		},
	end,
}

@[simp] lemma mem_filter_containing (A : set (set α)) (x : set α) : 
x ∈ filter_containing A ↔ x ∈ {B : set α | ∃(C) (C_ss : C ⊆ A) (C_fin : C.finite), ⋂₀ C ⊆ B}
:= iff.refl _

lemma subset_of_filter_containing (A : set (set α)) : A ⊆ (filter_containing A).sets :=
λ x _, ⟨{x}, by finish⟩

lemma smallest_filter_containing {A : set (set α)} : ∀(F : filter α), 
A ⊆ F.sets → (filter_containing A) ≤ F :=
begin 
	intros F h_ss B hB,
	rcases hB with ⟨C, C_ss, C_fin, hC⟩,
	have hCF := fin_inter_sets (subset.trans C_ss h_ss) C_fin,
	exact F.sets_of_superset hCF hC,
end

lemma filter_containing_proper_iff (A : set (set α)) : 
proper_filter (filter_containing A) ↔ fip A :=
begin 
	split,
	{
		intros h C hCA C_fin contra,
		apply h, rw ←contra,
		use [C, hCA, C_fin, subset_refl _],
	},
	{
		intros A_fip contra,
		rcases contra with ⟨C, C_ss, C_fin, hC⟩,
		apply A_fip C_ss C_fin,
		rwa subset_empty_iff at hC,
	},
end

def ultrafilter (F : filter α) := proper_filter F ∧ (∀A, A ∈ F ∨ Aᶜ ∈ F)
def maximal_proper_filter (F : filter α) := proper_filter F ∧
 ∀{G : filter α}, proper_filter G → F ≤ G → F = G

 lemma not_mem_ultrafilter_iff {F : filter α} (h : ultrafilter F) (x) : x ∉ F ↔ xᶜ ∈ F :=
 begin 
	split,
	{ have := (h.2) x, tauto },
	{
		intros hx contra,
		apply h.1,
		have : x ∩ xᶜ = ∅ := by finish,
		rw ←this,
		exact F.inter_sets contra hx
	},
 end

 lemma fip_insert_of_proper_filter {F : filter α} (F_proper : proper_filter F) (x : set α) :
 fip (insert x F.sets) ∨ fip (insert xᶜ F.sets) :=
 begin 
	suffices : (∀{y}, y ∈ F → y ∩ x ≠ ∅) ∨ (∀{y}, y ∈ F → y ∩ xᶜ ≠ ∅),
	{
		have h_wlog : ∀x : set α, (∀{z}, z ∈ F → z ∩ x ≠ ∅) → fip (insert x F.sets),
		{
			clear this x,
			intros x hA₁ A A_ss A_fin hA₂,
			have hxA : x ∈ A,
			{
				by_contra,
				have A_ss_F : A ⊆ F.sets,
				{
					intros y hy,
					have := A_ss hy,
					cases this, exfalso, rw this at hy, exact h hy,
					exact this,
				},
				have := fin_inter_sets A_ss_F A_fin,
				rw hA₂ at this,
				apply F_proper,
				exact this,
			},
			have triv : A = (A \ {x}) ∪ {x},
			{
				ext y,
				split;finish
			},
			rw [triv, sInter_union, sInter_singleton] at hA₂, clear triv,
			have A'_ss : A \ {x} ⊆ F.sets,
			{
				intros y hy,
				simp at hy,
				have := A_ss hy.1,
				simp at this ⊢,
				tauto,
			},
			have A'_fin : (A \ {x}).finite := finite.diff A_fin _,
			have hA'F := fin_inter_sets A'_ss A'_fin,
			exact hA₁ hA'F hA₂,
		},
		cases this,
		{ exact or.inl (h_wlog _ @this) },
		{ exact or.inr (h_wlog _ @this) },
	},
	
	by_contra h, push_neg at h,
	rcases h with ⟨⟨Y₁, Y₁F, Y₁_empty⟩, ⟨Y₂, Y₂F, Y₂_empty⟩⟩,
	have contra : Y₁ ∩ Y₂ = ∅,
	{
		rw eq_empty_iff_forall_not_mem at *,
		intros y hy,
		by_cases y ∈ x,
		{ exact Y₁_empty _ ⟨hy.1, h⟩ },
		{ exact Y₂_empty _ ⟨hy.2, h⟩ },
	},
	have inter_sets := F.inter_sets Y₁F Y₂F,
	rw contra at inter_sets,
	exact F_proper inter_sets,
 end


lemma ultrafilter_iff_maximal_proper_filter (F : filter α) : 
ultrafilter F ↔ maximal_proper_filter F :=
begin 
	split,
	{
		intros h, use [h.1],
		intros G G_proper hFG,
		apply le_antisymm, exact hFG,
		intros x hxG, simp,
		by_contra contra,
		apply G_proper,
		rw not_mem_ultrafilter_iff h x at contra,
		have contra1 := G.inter_sets hxG (hFG contra),
		have : x ∩ xᶜ = ∅ := by finish,
		rwa ←this,
	},
	{
		intro hF, use hF.1, intros x, by_contra hx, push_neg at hx,
		have hfip := fip_insert_of_proper_filter hF.1 x,
		cases hfip,
		{
			have F_le : F ≤ filter_containing (insert x F.sets),
			{
				intros y hy,
				exact subset_of_filter_containing _ (mem_insert_of_mem _ hy),
			},
			have := (filter_containing_proper_iff _).mpr hfip,
			have := (hF.2 this) F_le,
			apply hx.1,
			rw this,
			apply subset_of_filter_containing,
			exact mem_insert _ _,
		},
		{
			have F_le : F ≤ filter_containing (insert xᶜ F.sets),
			{
				intros y hy,
				exact subset_of_filter_containing _ (mem_insert_of_mem _ hy),
			},
			have := (filter_containing_proper_iff _).mpr hfip,
			have := (hF.2 this) F_le,
			apply hx.2,
			rw this,
			apply subset_of_filter_containing,
			exact mem_insert _ _,
		},
	}
end

theorem ultrafilter_of_proper_filter {F : filter α} (F_proper : proper_filter F) :
∃ {U : filter α} (hFU : F.sets ⊆ U.sets), ultrafilter U :=
begin 
	have F_fip : fip F.sets := by finish[(@fip_iff_proper_filter _ F).mpr F_proper],
	have := @exists_maximal_of_finite_character _ {G : set (set α) | fip G} F.sets F_fip _,
	swap,
	{
		exact λ G,
		⟨
			λ G_fip _ Y_ss Y_fin A A_ss A_fin, G_fip (subset.trans A_ss Y_ss) A_fin,
			λ hG _ A_ss A_fin, @hG _ A_ss A_fin _ (subset_refl _) A_fin 
		⟩
	},

	rcases this with ⟨U_sets, U_fip, hFU, U_max⟩,
	have U_filter : (filter_containing U_sets).sets = U_sets,
	{
		apply U_max, swap, exact subset_of_filter_containing U_sets,
		simp,
		rwa [fip_iff_proper_filter, filter_containing_proper_iff],
	},
	use filter_containing U_sets,
	rw U_filter,
	use hFU,
	rw ultrafilter_iff_maximal_proper_filter,
	use by rwa [←fip_iff_proper_filter, U_filter],

	intros G G_proper hG,
	unfold has_le.le at hG, rw U_filter at hG,
	rw ←fip_iff_proper_filter at G_proper,
	rw [←filter_eq, U_filter, eq_comm],
	exact U_max G_proper hG,
end

theorem ultrafilter_of_fip {A : set (set α)} (A_fip : fip A) : 
∃(U : filter α) (hAU : A ⊆ U.sets), ultrafilter U :=
begin 
	rcases ultrafilter_of_proper_filter ((filter_containing_proper_iff _).mpr A_fip)
	with ⟨U, hAU, hU⟩,
	exact ⟨U, subset_trans (subset_of_filter_containing A) hAU, hU⟩,
end

end ultrafilter