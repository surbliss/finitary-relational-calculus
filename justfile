default:
    @just --list

# Run hoogle
docs:
    echo http://127.0.0.1:8888
    hoogle serve -p 8888 --local

# Run cabal repl
repl *ARGS:
    cabal repl {{ ARGS }}

# Run ghcid -- auto-recompile and run `main` function
run:
    ghcid --command="ghci -isrc -iapp app/Main.hs" --run="main" --test-message="" -W -q


test:
    cabal test

watch:
    watchexec -e hs cabal test
