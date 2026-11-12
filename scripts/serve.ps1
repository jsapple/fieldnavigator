$root = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot ".."))
$mime = @{
  ".html" = "text/html; charset=utf-8"
  ".js" = "text/javascript; charset=utf-8"
  ".css" = "text/css; charset=utf-8"
  ".webmanifest" = "application/manifest+json"
  ".png" = "image/png"
  ".json" = "application/json"
}
$listener = New-Object System.Net.HttpListener
$listener.Prefixes.Add("http://127.0.0.1:4173/")
$listener.Start()
Write-Output "LISTENING http://127.0.0.1:4173/"
while ($listener.IsListening) {
  $context = $listener.GetContext()
  try {
    $path = [Uri]::UnescapeDataString($context.Request.Url.AbsolutePath)
    if ($path -eq "/") { $path = "/index.html" }
    $relative = $path.TrimStart("/") -replace "/", "\"
    $full = [System.IO.Path]::GetFullPath((Join-Path $root $relative))
    if (-not $full.StartsWith($root, [StringComparison]::OrdinalIgnoreCase)) {
      $context.Response.StatusCode = 403
    } elseif (Test-Path -LiteralPath $full -PathType Leaf) {
      $bytes = [System.IO.File]::ReadAllBytes($full)
      $ext = [System.IO.Path]::GetExtension($full).ToLowerInvariant()
      $type = $mime[$ext]
      if (-not $type) { $type = "application/octet-stream" }
      $context.Response.StatusCode = 200
      $context.Response.ContentType = $type
      $context.Response.ContentLength64 = $bytes.Length
      $context.Response.OutputStream.Write($bytes, 0, $bytes.Length)
    } else {
      $context.Response.StatusCode = 404
    }
  } catch {
    $context.Response.StatusCode = 500
  } finally {
    $context.Response.Close()
  }
}
