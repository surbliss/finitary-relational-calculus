{ inputs, ... }:

{
  flake = rec {
    templates.default = {
      description = "A batteries-included Haskell project template for Nix";
      path = builtins.path { path = inputs.self; };
      welcomeText = ''
        Please see https://srid.ca/boolean-database/start
      '';
    };

    # https://omnix.page/om/init.html#spec
    om.templates.boolean-database = {
      template = templates.default;
      params = [
        {
          name = "author";
          description = "Author name";
          placeholder = "Thomas Holme Surlykke";
        }
        {
          name = "package-name";
          description = "Name of the Haskell package";
          placeholder = "boolean-database";
        }
        {
          name = "vscode";
          description = "Include the VSCode settings folder (./.vscode)";
          paths = [ ".vscode" ];
          value = true;
        }
        {
          name = "github-ci";
          description = "Include GitHub Actions workflow configuration";
          paths = [ ".github" ];
          value = true;
        }
        {
          name = "nix-template";
          description = "Keep the flake template in the project";
          paths = [ "**/template.nix" ];
          value = false;
        }
      ];
      tests = {
        default = {
          params = {
            package-name = "foo";
            author = "John";
            vscode = false;
          };
          asserts = {
            source = {
              ".github/workflows/ci.yaml" = true;
              ".vscode" = false;
            };
            packages.default = {
              "bin/foo" = true;
            };
          };
        };
      };
    };
  };
}
