{ ... }:
{
  haskellProjects.default = {
    # Default settings. For other settings, see
    # https://flake.parts/options/haskell-flake.html
    devShell.tools = hp: { inherit (hp) cabal-gild; };
  };
}
