// Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
'use strict';
// Summarizes independently enforced native/parser controls. This is not a proof
// emitter; no expected native register or memory results are constructed here.
const fs = require('node:fs');
const assert = require('node:assert/strict');
const crypto = require('node:crypto');
assert.equal(process.argv.length, 2);
const read = name => JSON.parse(fs.readFileSync(name, 'utf8'));
const hash = name => crypto.createHash('sha256').update(fs.readFileSync(name)).digest('hex');
const binding = read('BINDING.json'), metadata = read('PROBES.json');
assert.equal(binding.format, 'rex-data32-native-v1');
assert.equal(metadata.format, binding.format);
assert.equal(binding.observations, 148);
assert.equal(binding.positive_probes, 37);
assert.equal(binding.capture_sha256, hash('captures.bin'));
assert.equal(binding.elf_sha256, hash('probe.elf'));
assert.equal(binding.whole_probe_and_capture_section_sha256, hash('linked-section.bin'));
assert.equal(binding.literal_metadata_sha256, hash('PROBES.json'));
const native = read('NATIVE-CONTROLS.json');
const parser = read('PARSER-CONTROLS.json');
const auth = read('AUTH-CONTROLS.json');
for (const [controls, count] of [[native, 16], [parser, 41], [auth, 15]]) {
    assert.equal(controls.length, count);
    assert.equal(new Set(controls.map(c => c.name)).size, count);
    assert.ok(controls.every(c => c.rejected === true));
}
const faults = native.filter(c => c.signal !== 0);
assert.equal(faults.length, 2);
for (const control of native) {
    if (control.signal) {
        assert.equal(control.signal, 11);
        assert.equal(control.exit, -1);
        assert.equal(control.capture_complete, false);
        assert.equal(control.fault_measured_before, null);
        assert.equal(control.fault_measured_after, null);
        assert.equal(fs.statSync(control.evidence).size, 3 * 4096);
    } else {
        assert.equal(control.exit, 1);
        assert.equal(control.capture_complete, true);
        assert.notEqual(control.mismatch_mask, 0);
        assert.equal(fs.statSync(control.evidence).size, 160 + 25056 + 16);
    }
}
assert.ok(auth.every(c => c.exit === 2));
assert.equal(parser.filter(c => c.rehash_to_test_semantics).length, 40);
assert.equal(metadata.probes.filter(p => p.positive).length, 37);
assert.equal(metadata.probes.length, 53);
const observations = fs.readFileSync('REPLAY-INPUTS.jsonl', 'utf8').trimEnd().split('\n').map(JSON.parse);
assert.equal(observations.length, 148);
assert.ok(observations.every(o => o.hardware_RIP === null && o.modeled_operand_read.bytes === 4));
console.log(JSON.stringify({
    schema: 'rex-data32-native-run-v1',
    status: 'PASS',
    capture_format: binding.format,
    observations: binding.observations,
    positive_probes: binding.positive_probes,
    rejected_native_controls: native.length,
    rejected_parser_controls: parser.length,
    rejected_authentication_controls: auth.length,
    native_fault_controls: faults.length,
    sha256: {
        elf: binding.elf_sha256,
        section: binding.whole_probe_and_capture_section_sha256,
        metadata: binding.literal_metadata_sha256,
        captures: binding.capture_sha256,
        observation_data: hash('REPLAY-INPUTS.jsonl')
    },
    scope: 'Native conformance and binding ONLY. No fresh Lean kernel replay, CPU/OS refinement or corpus credit.',
    provenance: 'runner.txt, commands.txt, platform.txt, tool-versions.txt, TOOLS.sha256 and limits/ record launch and compute provenance; they are not proof evidence.',
    completion: 'Read exit, postflight.exit, scope.txt and OUTPUTS.sha256 alongside this report.'
}, null, 2));
