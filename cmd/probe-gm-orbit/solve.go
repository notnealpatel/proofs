package main

// Stage 2 driver: run the emitted Sage script via `sager -c` and parse the
// JSON verdict. Per Hu7 (route A-hybrid): Go constructs, SageMath does Groebner
// over Q(sqrt 3). The solver result is the certified verdict for the pair.

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

// sagerDir is the bind-mount directory the `sager` wrapper exposes to its
// SageMath container; scripts must live here to be visible (per the wrapper's
// constraint). The Go driver writes each system's script here and runs it.
const sagerDir = "/home/neal/p/proofs/Sager"

// sageResult is the parsed JSON line emitted by the Sage driver.
type sageResult struct {
	Verdict      string              `json:"verdict"`
	Reason       string              `json:"reason,omitempty"`
	Groebner     []string            `json:"groebner,omitempty"`
	Dimension    *int                `json:"dimension,omitempty"`
	NumPoints    *int                `json:"num_points,omitempty"`
	Points       []map[string]string `json:"points,omitempty"`
	VarietyError string              `json:"variety_error,omitempty"`
}

// runSage writes the Sage script into the sager bind-mount directory and runs
// it as `sager Sager/<name>.sage`, returning the parsed JSON verdict. The script
// file must live under sagerDir to be visible to the container. The file is
// retained (named per orbit pair) as an auditable artifact.
func runSage(ctx context.Context, name, script string) (*sageResult, string, error) {
	if err := os.MkdirAll(sagerDir, 0o755); err != nil {
		return nil, "", fmt.Errorf("mkdir %s: %w", sagerDir, err)
	}
	fname := filepath.Join(sagerDir, name+".sage")
	if err := os.WriteFile(fname, []byte(script), 0o644); err != nil {
		return nil, "", fmt.Errorf("write %s: %w", fname, err)
	}
	rel := filepath.Join("Sager", name+".sage")
	cmd := exec.CommandContext(ctx, "sager", rel)
	cmd.Dir = "/home/neal/p/proofs"
	out, err := cmd.CombinedOutput()
	raw := string(out)
	if err != nil {
		return nil, raw, fmt.Errorf("sager failed: %w; output:\n%s", err, raw)
	}
	// The JSON verdict is the last non-empty line (Sage may print warnings).
	line := lastJSONLine(raw)
	if line == "" {
		return nil, raw, fmt.Errorf("no JSON verdict in sage output:\n%s", raw)
	}
	var res sageResult
	if err := json.Unmarshal([]byte(line), &res); err != nil {
		return nil, raw, fmt.Errorf("parse sage verdict %q: %w", line, err)
	}
	return &res, raw, nil
}

// lastJSONLine returns the last line of s that starts with '{'.
func lastJSONLine(s string) string {
	lines := strings.Split(s, "\n")
	for i := len(lines) - 1; i >= 0; i-- {
		t := strings.TrimSpace(lines[i])
		if strings.HasPrefix(t, "{") {
			return t
		}
	}
	return ""
}
