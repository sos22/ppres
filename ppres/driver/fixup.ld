/* Script for --shared -z combreloc: shared library, combine & sort relocs */
ENTRY(_entry)
SECTIONS
{
  /* Read-only sections, merged into text segment: */
  . = 0 + SIZEOF_HEADERS;
  .dynsym         : { *(.dynsym) }
  .dynstr         : { *(.dynstr) }
  .rel.dyn        :
    {
      *(.rel.text)
      *(.rel.rodata)
      *(.rel.data.rel.ro*)
      *(.rel.data)
      *(.rel.got)
      *(.rel.bss)
    }
  .rela.dyn       :
    {
      *(.rela.text)
      *(.rela.rodata)
      *(.rela.data)
      *(.rela.got)
      *(.rela.bss)
    }
  .rel.plt        : { *(.rel.plt) }
  .rela.plt       : { *(.rela.plt) }
  .plt            : { *(.plt) }
  .init           :
  {
    KEEP (*(.init))
  } =0x90909090
  .text           :
  {
    *(.text)
  } =0x90909090

  fixup_table : {
    first_fixup = .; PROVIDE(first_fixup = .);
    *(fixup_table)
    last_fixup = .; PROVIDE(last_fixup = .);
    }

  PROVIDE(__init_array_start = .);
  .init_array     :
  {
     KEEP (*(SORT(.init_array.*)))
     KEEP (*(.init_array))
  }
  PROVIDE(__init_array_end = .);

  .bss            :
  {
   *(.dynbss)
   *(.bss)
   *(COMMON)
   /* Align here to ensure that the .bss section occupies space up to
      _end.  Align after .bss to ensure correct alignment even if the
      .bss section disappears because there are no input sections.
      FIXME: Why do we need it? When there is no .bss section, we don't
      pad the .data section.  */
  }
  _end = .; PROVIDE (end = .);
}
