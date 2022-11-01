import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.basic

open function classical

namespace simple_graph

variables {V : Type*} {G : simple_graph V} {u v: V}


namespace walk

lemma split_cycle.aux {x y : V} (p : G.walk y x) (p' : G.walk x y)
  (pc : (p'.append p).is_cycle)
  {u v : V}
  (ep : (⟦⟨u,v⟩⟧ : sym2 V) ∈ p.edges)
  (ep' : (⟦⟨u,v⟩⟧ : sym2 V) ∉ p'.edges) :
  ∃ q : G.walk u v, (⟦⟨u,v⟩⟧ : sym2 V) ∉ q.edges := -- Could strengthen to `w` being a path but do I care?
begin
  induction p with _ a b c e q ih,
  { simp only [edges_nil, list.not_mem_nil] at ep,
    exact ep.elim, },
  { by_cases h' : u = a ∧ v = b,
    { rcases h' with ⟨rfl,rfl⟩,
      use (q.append p').reverse,
      simp_rw [reverse_append, edges_append, edges_reverse, list.mem_append, list.mem_reverse],
      rintro (ep''|eq'),
      { exact ep' ep'', },
      { let := pc.edges_nodup,
        rw [edges_append, edges_cons] at this,
        let := list.nodup.of_append_right this, rw [list.nodup_cons] at this,
        exact this.left eq', }, },
    { by_cases h'' : v = a ∧ u = b,
      { rcases h'' with ⟨rfl,rfl⟩,
        use q.append p',
        simp only [reverse_append, edges_append, edges_reverse, list.mem_append, list.mem_reverse],
        rintro (eq'|ep''),
        { let := pc.edges_nodup, rw [edges_append, edges_cons] at this,
          let := list.nodup.of_append_right this, rw [list.nodup_cons, sym2.eq_swap] at this,
          exact this.left eq', },
        { exact ep' ep'', },
      },
      { have : (⟦(u, v)⟧ : sym2 V) ∈ q.edges, by
        { simp only [edges_cons, list.mem_cons_iff, quotient.eq, sym2.rel_iff] at ep,
          rcases ep with ((one|two)|three),
          exact (h' one).elim, exact (h'' ⟨two.right,two.left⟩).elim, exact three, },
        apply @ih (p'.append e.to_walk),
        { rw [←walk.append_assoc], simp only [cons_nil_append], exact pc, },
        { exact this, },
        { simp only [edges_append, edges_cons, edges_nil, list.mem_append, list.mem_singleton,
                     quotient.eq, sym2.rel_iff],
          rintro (one|(two|three)),
          exact ep' one, exact h' two, exact h'' ⟨three.2,three.1⟩, }, }, }, },
end

lemma split_cycle {x : V} {p : G.walk x x} (pc : p.is_cycle)
  {u v : V} (ep : (⟦⟨u,v⟩⟧ : sym2 V) ∈ p.edges) :
  ∃ q : G.walk u v, (⟦⟨u,v⟩⟧ : sym2 V) ∉ q.edges :=
begin
  apply split_cycle.aux p nil,
  { rw [nil_append], exact pc, },
  { exact ep, },
  { rintro h, simpa only [edges_nil, list.not_mem_nil] using h, },
end

end walk

end simple_graph
