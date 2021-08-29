let
  # Read in the Niv sources
  sources = {
    haskellNix = builtins.fetchTarball "https://github.com/input-output-hk/haskell.nix/archive/master.tar.gz";
  };

  # Fetch the haskell.nix commit we have pinned with Niv
  haskellNix = import sources.haskellNix {};

  # Import nixpkgs and pass the haskell.nix provided nixpkgsArgs
  pkgs = import
    haskellNix.sources.nixpkgs-2009
    haskellNix.nixpkgsArgs;
in pkgs.haskell-nix.project {
  # 'cleanGit' cleans a source directory based on the files known by git
  src = pkgs.haskell-nix.haskellLib.cleanGit {
    name = "haskell-nix-project";
    src = ./.;
  };
  # Specify the GHC version to use.
  compiler-nix-name = "ghc9001"; # Not required for `stack.yaml` based projects.
}
