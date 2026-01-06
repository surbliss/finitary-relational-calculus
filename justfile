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
    ghcid -T :main --test-message="" -W -q


# Use 'inter' (for interactive) in Main as a repl
inter:
    ghcid -T :inter


test:
    cabal test

watch:
    watchexec -e hs cabal test
