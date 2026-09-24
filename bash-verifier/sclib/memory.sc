type ptr = u64

element mem_root()
element mem_byte(addr : ptr)

attribute mem_val : u8
attribute alloc_ptr : ptr // A "pointer" to the first unallocated byte

fn malloc(size : u64) -> ptr {
  let res = mem_root().alloc_ptr;
  mem_root().alloc_ptr = mem_root().alloc_ptr + size;
  // We intentionally not set mem_bytes for the newly allocated memory
  return res;
}

// TODO: range as a builtin function
fn range(x : u64, y : u64) -> list::<u64> { assert false; }

fn calloc(size : u64) -> ptr {
  let res = malloc(size);
  for i in range(0u64, size) { mem_root().mem_byte(res + i).mem_val = 0u8; }
  return res;
}

// TODO: bytes as a builtin function
fn bytes<a>() -> u64 { assert false; }
// TODO: of_bytes as a builtin function
fn of_bytes<a>(x : list::<u8>) -> a { assert false; }

fn read<a>(addr : ptr) -> a {
  let bytes = for i in range(0u64, bytes::<a>()) {
    yield mem_root().mem_byte(addr + i).mem_val;
  };
  return of_bytes::<a>(bytes);
}

// TODO: get_byte as a builtin function (gets the ith byte of x)
fn get_byte<a>(x : a, i : u64) -> u8 { assert false; }

fn write<a>(addr : ptr, x : a) {
  for i in range(0u64, bytes::<a>()) {
    mem_root().mem_byte(addr + i).mem_val = get_byte::<a>(x, i);
  }
}
