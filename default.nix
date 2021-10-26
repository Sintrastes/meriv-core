let
  sources = import ./nix/sources.nix {};
  haskellNix = import sources.haskellNix {};

  pkgs = import
    haskellNix.sources.nixpkgs-unstable
    haskellNix.nixpkgsArgs;
in pkgs.haskell-nix.project {
  src = pkgs.haskell-nix.haskellLib.cleanGit {
    name = "meriv-core";
    src = ./.;
  };
  compiler-nix-name = "ghc8107";
}
