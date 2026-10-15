# Toccata 101

A collection of cards walking through what the Toccata hardfork changed in Kaspa, and what a single KAS
(or a single sompi) can do now. One concept per card, Kaspa's own terms defined once, and a real transaction
to open at the end wherever one exists.

**Read them here:** https://fingersllm.github.io/toccata-101/

Feel free to use this collection to make posts, videos or anything else that broadens Toccata
understanding — everything here is released under CC0 1.0, so no permission is needed. Found a mistake?
Open an issue and we'll fix it.

## The campaign's launch proof

The contribution page, [Deploy more Fingers](https://fingersllm.github.io/toccata-101/deploy.html), runs one
campaign on Kaspa mainnet. Anyone can check that it was launched the way the page says.

- Launch transaction: `5a8ade87bc12e223e6f231990869c7270526076148593a164f2d0432470cb23e`
- Campaign id: `2be2706a18302144f49323561c97d87a7af82b89f56f8df13855ed783f066300`

With Python 3.8 or later, in a copy of this repository, run:

```
python campaign/tools/p2r-vault/launch-proof.py campaign/real.constants.json 5a8ade87bc12e223e6f231990869c7270526076148593a164f2d0432470cb23e
```

It reads the launch transaction from api.kaspa.org and prints PROVEN only if all five hold:

1. The campaign is born in that transaction.
2. Exactly one output carries its id, so there is one vault, not two.
3. The id is the one the network computes.
4. The vault runs the contracts published here, with the page's settings, open and empty.
5. The settings are valid, and the vault holds enough to pay its own fees.

If you do not want to trust api.kaspa.org, add `--api` with the address of another server that runs the same API.
The contracts' sources and compiled bytes are in `campaign/contracts/p2r-vault/`, compiled with silverc v1.0.0.
