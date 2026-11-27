// SPDX-License-Identifier: Apache-2.0
#![forbid(unsafe_code)]
use asm_core::*;
use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();
    let out_path = if args.len() > 2 && args[1] == "--json" {
        Some(args[2].clone())
    } else {
        None
    };

    let a1 = audit_apollonian_packing([-3, 5, 8, 8], 1_000);
    let a2 = audit_apollonian_packing([-7, 17, 12, 20], 1_000);
    let a3 = audit_apollonian_packing([-11, 21, 24, 28], 1_000);
    let au = audit_apollonian_packing([-4, 8, 9, 9], 1_000);
    let oct_obs = audit_octahedral_packing([-6, 10, 17, 40, 24, 17], 1_500);
    let oct_str = audit_octahedral_packing([0, 0, 1, 2, 2, 1], 400);
    let (s3_q, s3_b, s3_sq, s3_ok) = audit_soddy3_packing([-6, 13, 13, 13, 18], 150);

    let det_z2_2 = exact_det_bareiss(&grid_laplacian_matrix(LatticeKind::SquareZ2, 2));
    let det_z2_3 = exact_det_bareiss(&grid_laplacian_matrix(LatticeKind::SquareZ2, 3));
    let det_a2_2 = exact_det_bareiss(&grid_laplacian_matrix(LatticeKind::TriangularA2, 2));
    let det_a2_3 = exact_det_bareiss(&grid_laplacian_matrix(LatticeKind::TriangularA2, 3));
    let (e_z2_15, conf_z2, idem_z2, top_z2) = compute_dhar_identity(LatticeKind::SquareZ2, 15);
    let (e_a2_15, conf_a2, idem_a2, top_a2) = compute_dhar_identity(LatticeKind::TriangularA2, 15);

    let mk = audit_markov_tree(10_000_000);
    let (c1, c2, c3, c4, c5) = markov_cluster_numerators(1, 1, 1);
    let hw = audit_hurwitz_n4(8, 120);

    let json = format!(
        concat!(
            "{{\n",
            "  \"pillar1\": {{\n",
            "    \"hkrs_root1\": {{\"quads\": {}, \"bends\": {}, \"squares\": {}, \"chi_m1\": {}, \"chi_p1\": {}, \"mod24\": {:?}}},\n",
            "    \"hkrs_root2\": {{\"quads\": {}, \"bends\": {}, \"squares\": {}, \"chi_m1\": {}, \"chi_p1\": {}, \"mod24\": {:?}}},\n",
            "    \"hkrs_root3\": {{\"quads\": {}, \"bends\": {}, \"squares\": {}, \"chi_m1\": {}, \"chi_p1\": {}, \"mod24\": {:?}}},\n",
            "    \"unobstructed_4899\": {{\"quads\": {}, \"bends\": {}, \"squares\": {}, \"mod24\": {:?}}},\n",
            "    \"octahedral_obstructed\": {{\"sextuples\": {}, \"bends\": {}, \"pow2_squares\": {}, \"mod8_locked\": {}, \"odd_jacobi_m1\": {}, \"mod24\": {:?}}},\n",
            "    \"octahedral_strip\": {{\"sextuples\": {}, \"bends\": {}, \"squares\": {}, \"double_squares\": {}, \"mod24\": {:?}}},\n",
            "    \"soddy3d_contrast\": {{\"quintuples\": {}, \"bends\": {}, \"squares\": {}, \"all_q0\": {}}}\n",
            "  }},\n",
            "  \"pillar2\": {{\n",
            "    \"det_z2_2x2\": {},\n",
            "    \"det_z2_3x3\": {},\n",
            "    \"det_a2_2x2\": {},\n",
            "    \"det_a2_3x3\": {},\n",
            "    \"z2_15x15\": {{\"confluent\": {}, \"idempotent\": {}, \"topplings\": {}, \"sum_chips\": {}}},\n",
            "    \"a2_15x15\": {{\"confluent\": {}, \"idempotent\": {}, \"topplings\": {}, \"sum_chips\": {}}}\n",
            "  }},\n",
            "  \"pillar3\": {{\n",
            "    \"markov_max_val\": {},\n",
            "    \"triples_count\": {},\n",
            "    \"distinct_numbers\": {},\n",
            "    \"uniqueness_holds\": {},\n",
            "    \"all_odd_mod4_eq1\": {},\n",
            "    \"all_even_mod32_eq2\": {},\n",
            "    \"even_mod64_residues\": {:?},\n",
            "    \"odd_prime_mod4_violations\": {},\n",
            "    \"all_pairwise_coprime\": {},\n",
            "    \"cluster_5step_at_111\": [{}, {}, {}, {}, {}],\n",
            "    \"hurwitz_n4_le120_counts\": {{\"a1\": {}, \"a2\": {}, \"a3\": {}, \"a4\": {}, \"a5_to_8\": {}}}\n",
            "  }}\n",
            "}}\n"
        ),
        a1.quads_visited, a1.distinct_bends, a1.square_hits.len(), a1.chi_minus1_count, a1.chi_plus1_count, a1.mod24_residues,
        a2.quads_visited, a2.distinct_bends, a2.square_hits.len(), a2.chi_minus1_count, a2.chi_plus1_count, a2.mod24_residues,
        a3.quads_visited, a3.distinct_bends, a3.square_hits.len(), a3.chi_minus1_count, a3.chi_plus1_count, a3.mod24_residues,
        au.quads_visited, au.distinct_bends, au.square_hits.len(), au.mod24_residues,
        oct_obs.sextuples_visited, oct_obs.distinct_bends, oct_obs.pow2_square_hits.len(), oct_obs.all_mod8_locked, oct_obs.all_odd_jacobi_minus1, oct_obs.mod24_residues,
        oct_str.sextuples_visited, oct_str.distinct_bends, oct_str.square_hits.len(), oct_str.double_square_hits.len(), oct_str.mod24_residues,
        s3_q, s3_b, s3_sq.len(), s3_ok,
        det_z2_2, det_z2_3, det_a2_2, det_a2_3,
        conf_z2, idem_z2, top_z2, e_z2_15.iter().sum::<i32>(),
        conf_a2, idem_a2, top_a2, e_a2_15.iter().sum::<i32>(),
        mk.max_val, mk.triples_count, mk.distinct_markov_numbers, mk.uniqueness_holds,
        mk.all_odd_mod4_eq1, mk.all_even_mod32_eq2, mk.even_mod64_residues,
        mk.odd_prime_mod4_violations, mk.all_pairwise_coprime,
        c1, c2, c3, c4, c5,
        hw[&1].len(), hw[&2].len(), hw[&3].len(), hw[&4].len(),
        hw[&5].len() + hw[&6].len() + hw[&7].len() + hw[&8].len()
    );

    if let Some(p) = out_path {
        fs::write(&p, &json).expect("write json");
    } else {
        print!("{}", json);
    }
}
