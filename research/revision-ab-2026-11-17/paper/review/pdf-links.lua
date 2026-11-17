function Link(el)
  if not el.target:match("^https?://") and not el.target:match("^#") then
    return el.content
  end
end
