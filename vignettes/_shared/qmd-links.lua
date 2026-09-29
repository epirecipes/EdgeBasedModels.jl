-- Rewrite relative links to other vignette pages (`E01_.../index.qmd`) to the rendered file of
-- the current format: `.html` for html (and pdf, whose links point at the html pages), `.md`
-- for gfm. A default-type quarto project does not do this itself (only websites and books do).
function Link(el)
  if el.target:match("^%a[%w+.-]*:") then return nil end   -- absolute URL: leave alone
  local ext = quarto.doc.is_format("gfm") and ".md" or ".html"
  local new, n = el.target:gsub("%.qmd(#?.*)$", ext .. "%1")
  if n > 0 then el.target = new; return el end
end
