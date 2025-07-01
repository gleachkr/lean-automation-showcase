# lean-automation-showcase

You'll need `elan` the lean toolchain manager installed to use this.

Run `lake update` to download dependencies. It will take quite a while.

Run `lake build` to build them. This will also take a minute, and it will show 
some errors since Main.lean contains some deliberately incorrect examples.

But then you should be able to open Main.lean in an editor that supports the 
lean LSP and explore the slides (including the high-powered prover invocations) 
interactively!
