# Documentation and example tests

The `Documentation` GitHub Actions workflow builds HTML on pull requests,
pushes to `master`, and manual runs. Download `documentation-html` from a
successful run and open `index.html`. It does not publish a website.

On Linux, install LDC and ldmd2 **1.43.0**, Git, Ninja, and Python 3.9+ with
pip. From the repository root, use a fresh output directory:

```sh
python3 tools/build_docs.py build/docs
python3 -m http.server --directory build/docs/site 8000
```

The driver clones build inputs and overlays tracked working-tree edits,
including staged additions and deletions. It retains logs, inputs, isolated
Python dependencies, and a version manifest without modifying the checkout.
Meson 0.61.1, semver 2.13.0, and the circle-dlang asset revision are pinned.
HTML compilation treats warnings as errors. Release tags are required by
the template; both workflows fetch full history and tags.

LDC 1.43.0 is pinned for this repository. LDC 1.36.0 fails an existing
compile-time exception-message assertion when DIP1008 tests are enabled.

## Library and extracted-example tests

The separate `Meson tests` workflow runs the D library suite and extracted
documentation examples with `mir_core_test` and the DIP1008 compiler option:

```sh
python3 tools/build_docs.py build/meson-tests --tests-with-examples
```

The template builds HTML alongside the extracted example executables.
Every test configured by Meson must run successfully. The driver requires
the library test and at least one extracted-example suite, rejects skipped
tests, and does not hard-code the example count. Build and test logs are
uploaded as `meson-test-logs` even on failure.

The driver creates the pinned extractor's default `out` directory before
starting parallel example extraction. Single-file results go to stdout, but
the extractor still creates this directory and otherwise races on first use.
All build modes retain two Ninja build jobs.

Use `--tests-only` for library tests without HTML or extracted examples.
Run `python3 tools/test_build_docs.py` for driver regression checks.

The existing compiler matrix and CircleCI release publishing remain separate.
An HTML build does not verify every link or the external online example runner.
