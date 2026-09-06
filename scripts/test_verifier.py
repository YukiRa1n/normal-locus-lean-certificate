"""Failure-path tests for the frozen-file guard; temporary fixtures are not proof modules."""

from pathlib import Path
import hashlib
import json
import tempfile
import unittest

from verify import check_manifest


class FrozenSourceGuard(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / "NormalLocus").mkdir()
        self.source = self.root / "NormalLocus/Test.lean"
        self.source.write_text("def reviewedValue := 1\n", encoding="utf-8")
        (self.root / "manifest.json").write_text(json.dumps({"files": {
            "NormalLocus/Test.lean": hashlib.sha256(self.source.read_bytes()).hexdigest()
        }}), encoding="utf-8")

    def test_original_snapshot_is_accepted(self):
        check_manifest(self.root)

    def test_modified_definition_is_rejected(self):
        self.source.write_text("def reviewedValue := 2\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "Reviewed file changed"):
            check_manifest(self.root)

    def test_unregistered_module_is_rejected(self):
        (self.root / "NormalLocus/Unexpected.lean").write_text("", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "source file set differs"):
            check_manifest(self.root)

    def test_missing_reviewed_file_is_rejected(self):
        manifest = json.loads((self.root / "manifest.json").read_text(encoding="utf-8"))
        manifest["files"]["missing-reviewed-document.md"] = "0" * 64
        (self.root / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "Reviewed file changed"):
            check_manifest(self.root)


if __name__ == "__main__":
    unittest.main()
