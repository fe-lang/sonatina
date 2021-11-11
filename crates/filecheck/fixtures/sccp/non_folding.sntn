#! Assert no constant is never folded.

# sameln: func %non_folding(v0.i64):
# nextln:    block1:
# nextln:        v2.i64 = imm_u64 1;
# nextln:        v3.i64 = load v0 i64;
# nextln:        v4.i64 = add v2 v0;
# nextln:        v5.i64 = add v2 v3;
func %non_folding(v0.i64):
    block1:
        v2.i64 = imm_u64 1;
        v3.i64 = load v0 i64;
        v4.i64 = add v2 v0;
        v5.i64 = add v2 v3;
