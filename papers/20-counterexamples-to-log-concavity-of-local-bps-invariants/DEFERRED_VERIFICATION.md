# Verification scope

The complete finite calculation and its final concrete exports require verification from the current sources. The RContent 36 root assembly was interrupted with exit 130 and produced no root compiled artifact. Its 36 branch modules had compiled individually. The final 393-row assembly, complete defining-module audit, 22 fixed relative statements and their negative controls have not all been checked together at the current inputs.

The conditional transfers expose the exact finite-root premise; they do not replace that calculation. This is a paper-owned finite check, not an imported external theorem. The unconditional final theorem exports are not supplied. The README and `EXTERNAL_DEPENDENCIES.md` describe the separate external mathematical inputs.

Prepare the registered generated sources explicitly, then run the shared build and fixed relative checks from the repository root:

```sh
python3 scripts/prepare.py --paper 20 --execute
python3 scripts/verify.py --paper 20 --check build
python3 scripts/verify.py --paper 20 --check comparator --local
python3 scripts/verify.py --paper 20 --check comparator --suite negative-premise --local
python3 scripts/verify.py --paper 20 --check comparator --suite negative-axiom --local
```

Generation, compilation and kernel replay are distinct checks. These commands are provided for reproduction; they have not been rerun during repository preparation.
