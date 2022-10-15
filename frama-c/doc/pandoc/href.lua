function Link(el)
  el.target = string.gsub(el.target, "%.md", ".md.html")
  return el
end
