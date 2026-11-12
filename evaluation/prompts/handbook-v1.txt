Translate the final natural-language request into Astrogator FQL. Return only the query, without Markdown or explanations. Preserve every stated condition, path, string, user, group, and action. Do not add unstated operations. The following is a source-derived language reference, not a list of target answers.

LEXICAL AND CONTROL-FLOW RULES
Keywords are lower case; OS names are case sensitive. Quote literal paths, URLs, versions, and text with double quotes. Quoted strings have no escape processing: a literal newline is permitted, but backslash-n denotes two characters. There is no escaping a double quote inside a string. A question-mark-prefixed identifier such as ?path is an unknown; use it only for genuinely unspecified values, never to replace a supplied literal.

A query is zero or more period-separated statements, but a useful output must be nonempty. An atomic statement has an action followed by arguments. Semicolons sequence atomic actions, and a conditional may follow a semicolon. Periods terminate statements and reset the semantic OS context. Conditional syntax is `if CONDITION then STATEMENT otherwise STATEMENT`; `otherwise` is optional. There are no parentheses, braces, end, or fi tokens. An otherwise branch binds to the nearest unmatched if. Conditions can be joined with `and` or `or` (and binds more tightly). Carefully preserve scope: a period after a guarded statement makes the following statement unconditional.

Arguments use the separators at, for, from, in, into, to, via, with. A separator followed by a value gives that separator's argument; e.g. `at "/srv/example"`. Named arguments use `with name="example", primary group="staff"`; their separator does not become the argument name. Multiword names such as `supplemental groups` and `list directory` are separate unquoted words. Commas separate named argument definitions, not sequence items or list members. List values are whitespace-separated, e.g. `supplemental groups="staff" "operators"`.

PATHS AND FILE METADATA
A path is a single quoted value, or `remote "PATH"`, or `controller "PATH"`. A bare path means the remote managed host. Controller must be explicitly requested; remote/controller is not a literal keyword. Literal paths are not appended to categories: use `create directory at "PATH"`, not `create directory "PATH"`.

Where supported below, file metadata consists of optional `owner="USER"`, `group="GROUP"`, `read=owner group other`, `write=owner`, `execute=owner group`, `list directory=owner group`, `setuid=true`, `setgid=false`, `sticky=true`. Permission subjects are owner, group, other, or all. Values enumerate exactly the subjects having that permission; an absent permission argument is unspecified, not false. Octal `mode` is not an FQL argument. To express no subjects for one permission, an empty value is NOT legal syntax; do not invent `none`. `list directory` is a separate permission field. Some requests may exceed what this language can express.

ACTION SIGNATURES
The following placeholders must be replaced with requested literals. Optional arguments are described in prose, not bracket syntax to emit.

Files and directories:
- `create file at "PATH"`; optional content="TEXT" and file metadata.
- `create directory at "PATH"`; optional file metadata.
- `delete file at "PATH"` and `delete directory at "PATH"`; no recursive argument.
- `delete files in "DIRECTORY"`; optional glob="PATTERN".
- `copy file from "SOURCE" to "DESTINATION"`, `copy directory from "SOURCE" to "DESTINATION"`, or `copy files from "DIRECTORY" to "DIRECTORY"`; all accept file metadata, plural files additionally accept glob="PATTERN".
- `move file from "SOURCE" to "DESTINATION"`, `move directory from "SOURCE" to "DESTINATION"`, or `move files from "DIRECTORY" to "DIRECTORY"`; metadata and plural glob as for copy.
- `download file from "URL" to "PATH"`; optional file metadata.
- `write "TEXT" to "PATH" with position=overwrite`; position is REQUIRED and may be overwrite, top/start, or bottom/end. Optional file metadata. Do not substitute create for overwrite or append without checking the request.
- `set file permissions for "PATH" with read=all, write=owner`; accepts permission fields only, not owner/group. `in "DIRECTORY"` instead of `for "PATH"` selects files in a directory.

Identity and privileges:
- `create user with name="USER"`; optional primary group="GROUP" and supplemental groups="GROUP1" "GROUP2".
- `delete user with name="USER"`.
- `create group with name="GROUP"` and `delete group with name="GROUP"`.
- `disable password for user="USER"`; this is a distinct modeled action from setting a login shell.
- `enable sudo for user="USER"`, `disable sudo for user="USER"`, `enable passwordless sudo for group="GROUP"`, `disable passwordless sudo for group="GROUP"`. All four forms require exactly one user or group.
- `set default shell for user="USER" to bash` or `to zsh`. Shell names are resolved by the knowledge base, not arbitrary executable paths.
- `create ssh key for user="USER" with name="KEYNAME"`; alternatively use at "PATH" instead of name. Exactly one of at and name is required; user is required in either case.

Packages, services, repositories, and environment:
- `install PACKAGE`; optional version="VERSION". `uninstall PACKAGE`. PACKAGE is a knowledge-base description from the catalog below, not the word package followed by an arbitrary name. Do not invent apt, pip, manager, or package-name arguments.
- `start SERVICE service` and `stop SERVICE service`; SERVICE is a knowledge-base description below. Service enable-at-boot is not a supported action.
- `clone git repository from "URL" into "PATH"`; optional branch="BRANCH" OR tag="TAG", not both, and file metadata.
- `clone github repository with name="ORG/REPO" into "PATH"`; optional via ssh or via https (default), branch or tag, and metadata. URLs with and without .git are represented as alternatives.
- `create virtual environment in "PATH"`; optional python="VERSION".
- `set environment variable VARIABLE to "VALUE"`.
- `reboot`; no arguments.

SUPPORTED CONDITIONS AND OS CONTEXT
- `if os is Debian then ...`, Ubuntu, RedHat, `Debian based`, or `RedHat based`. Exact distribution and family are different. Preserve which the request says. `is not`, `equals`, and `not equals` are also accepted. Only OS equality is implemented; arbitrary variable equality is not supported.
- `if file "PATH" exists then ...`, `if directory "PATH" not exists then ...`; `file at "PATH"` and `directory at "PATH"` are alternatives. Named file/directory descriptions below also work.
- `if PACKAGE installed then ...` or `not installed`, using the package catalog.
- `if SERVICE running then ...` or `not running`, using the service catalog WITHOUT a trailing service keyword unless that keyword belongs to the catalog name.
- `if reboot required then ...` or `not required` requires an enclosing Debian, Ubuntu, or Debian based OS condition. It is unsupported for RedHat or unknown OS. The KB interprets this as presence of either /var/run/reboot-required or /run/reboot-required.

An OS conditional refines the semantic context inside its branches. Package and service descriptions that depend on OS must appear within a supported OS branch. A top-level earlier OS statement does not establish OS context for later period-separated statements. Do not omit a requested runtime guard merely to make semantic processing succeed.

KNOWLEDGE-BASE CATALOG (EXHAUSTIVE FOR THE PINNED EXAMPLE KB)
Packages:
- bash, zsh, postfix: system package manager, same name.
- apache or apache server: requires OS; Debian/Ubuntu/Debian based resolves to apt apache2, RedHat/RedHat based to dnf httpd.
- ssh client: requires OS; Debian side apt openssh-client, RedHat side dnf openssh-clients.
- ssh server: system openssh-server; no OS needed.
- numpy: system-wide requires OS. Debian/Debian based uses apt python3-numpy. Ubuntu also permits pip numpy. RedHat side permits pip numpy, dnf numpy, or dnf python3-numpy.
- `numpy in virtual environment at "PATH"`: pip numpy in that environment; no OS needed.
These are the only package descriptions in this KB. Resolving an OS-dependent description is different from hard-coding one of its concrete package names, which may be unsupported as FQL.

Services:
- ssh server: permits names sshd or ssh, no OS needed.
- postfix: postfix, no OS needed.
- apache server: requires OS, resolving to apache2 on Debian side or httpd on RedHat side.

Named files (append the word file to these descriptions):
- postfix configuration: /etc/postfix/main.cf.
- apache server html home page: /var/www/html/index.html.
- apache server php home page: /var/www/html/index.php.
- bash configuration or bashrc: .bashrc in the home of the required user="USER".
- zsh configuration or zshrc: .zshrc in the home of the required user="USER".
Named directory: `zsh configuration directory for user="USER"` resolves to .zshrc.d in that user's home.
These descriptions can replace a path where an action resolves a named resource. For example, `create bash configuration file for user="USER"`; `write "TEXT" to bash configuration file for user="USER" with position=end`; `copy postfix configuration file to "BACKUP"` uses the named file as source. Do not mix an explicit create-at path with a named resource description. For copy/move one missing from/to endpoint can be supplied by the named resource, not both. No named plural file collections are defined.

FINAL SELF-CHECK
Use only supported operations and arguments. Retain literal text exactly, including real newlines and trailing slashes when stated. Distinguish a directory from files inside it, copying from creating, and a conditional action from an unconditional one. Check every requested obligation against an action or condition in the query. Do not rely on syntactic validity as evidence that the request has been captured.
