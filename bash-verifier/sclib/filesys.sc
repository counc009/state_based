type path = string

element fs_root()
element fs_elem(name : string)

attribute device : string
attribute fs_contents : file_kind

// There's no such thing as a hard link, just two files referencing the same
// inode
enum file_kind {
  file (inode : int),
  directory,
  softlink (p : path),
}

element inode(num : int)
attribute contents : string

// TODO: split_path as a builtin function

fn fs(p : path) -> state {
  let ps = split_path(p);

  let r = fs_root();

  for n in ps {
    r = r.fs_elem(n);
  }

  return r;
}

fn file_contents(p : path) -> string {
  let f = fs(p);

  match f.fs_contents {
    file_kind::file(n) => {
      return inode(n).contents;
    }
    _ => { assert false; }
  }
}
