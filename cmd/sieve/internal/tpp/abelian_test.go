package tpp

import (
	"testing"
)

func TestAbelianLatticeZ2(t *testing.T) {
	// Z/2 has 2 subgroups: {0}, {0,1}.
	lat := AbelianLattice([]int{2})
	if len(lat) != 2 {
		t.Fatalf("Z/2: got %d subgroups, want 2", len(lat))
	}
}

func TestAbelianLatticeZ4(t *testing.T) {
	// Z/4 has 3 subgroups: {0}, {0,2}, {0,1,2,3}.
	lat := AbelianLattice([]int{4})
	if len(lat) != 3 {
		t.Fatalf("Z/4: got %d subgroups, want 3", len(lat))
	}
}

func TestAbelianLatticeZ2xZ2(t *testing.T) {
	// Z/2 x Z/2 has 5 subgroups: {0}, three copies of Z/2, and the whole group.
	lat := AbelianLattice([]int{2, 2})
	if len(lat) != 5 {
		t.Fatalf("Z/2 x Z/2: got %d subgroups, want 5", len(lat))
	}
}

func TestAbelianLatticeZ6(t *testing.T) {
	// Z/6 ~ Z/2 x Z/3 has 4 subgroups: 1, Z/2, Z/3, Z/6.
	lat := AbelianLattice([]int{6})
	if len(lat) != 4 {
		t.Fatalf("Z/6: got %d subgroups, want 4", len(lat))
	}
}

func TestAbelianLatticeZ2xZ2xZ2(t *testing.T) {
	// Z/2^3 has 16 subgroups.
	lat := AbelianLattice([]int{2, 2, 2})
	if len(lat) != 16 {
		t.Fatalf("Z/2^3: got %d subgroups, want 16", len(lat))
	}
}

func TestAbelianLatticeTrivial(t *testing.T) {
	lat := AbelianLattice(nil)
	if len(lat) != 1 {
		t.Fatalf("trivial: got %d subgroups, want 1", len(lat))
	}
	if lat[0].Order != 1 {
		t.Fatalf("trivial: subgroup order %d, want 1", lat[0].Order)
	}
}

func TestAbelianLatticeZ3xZ3(t *testing.T) {
	// Z/3 x Z/3 has 6 subgroups: 1, four copies of Z/3, and the whole group.
	lat := AbelianLattice([]int{3, 3})
	if len(lat) != 6 {
		t.Fatalf("Z/3 x Z/3: got %d subgroups, want 6", len(lat))
	}
}

func TestAbelianLatticeZ2xZ4(t *testing.T) {
	// Z/2 x Z/4 has 8 subgroups (validated against GAP).
	lat := AbelianLattice([]int{2, 4})
	if len(lat) != 8 {
		t.Fatalf("Z/2 x Z/4: got %d subgroups, want 8", len(lat))
	}
}

func TestAbelianLatticeZ2xZ2xZ3(t *testing.T) {
	// Z/2 x Z/2 x Z/3 has 10 subgroups (validated against GAP).
	lat := AbelianLattice([]int{2, 2, 3})
	if len(lat) != 10 {
		t.Fatalf("Z/2 x Z/2 x Z/3: got %d subgroups, want 10", len(lat))
	}
}

func TestPackUnpackRoundtrip(t *testing.T) {
	invs := []int{6, 4, 3}
	v := []int{5, 3, 2}
	pk := packVec(v, invs)
	got := unpackVec(pk, invs)
	for i := range v {
		if got[i] != v[i] {
			t.Errorf("component %d: got %d, want %d", i, got[i], v[i])
		}
	}
}
