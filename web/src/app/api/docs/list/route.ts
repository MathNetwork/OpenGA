import fs from 'node:fs'
import path from 'node:path'
import { resolveFs } from '@/lib/server/paths'

export const dynamic = 'force-dynamic'
export const runtime = 'nodejs'

/** First `# ` heading of an mdx file, else the filename stem. */
function mdxTitle(filePath: string): string {
  try {
    for (const raw of fs.readFileSync(filePath, 'utf8').split('\n')) {
      const line = raw.trim()
      if (line.startsWith('# ')) return line.slice(2).trim()
      if (line && !line.startsWith('---')) break
    }
  } catch { /* ignore */ }
  return path.basename(filePath).replace(/\.[^.]+$/, '')
}

export async function GET(req: Request) {
  const { searchParams } = new URL(req.url)
  const projectPath = searchParams.get('path')
  if (!projectPath) return Response.json({ detail: 'path required' }, { status: 400 })

  const docsDir = path.join(resolveFs(projectPath), '.astrolabe', 'docs')
  if (!fs.existsSync(docsDir)) return Response.json({ files: [] })

  const files = fs.readdirSync(docsDir)
    .filter((n) => (n.endsWith('.mdx') || n.endsWith('.md')))
    .sort()
    .map((n) => {
      const fp = path.join(docsDir, n)
      return { name: n, path: fp, title: mdxTitle(fp) }
    })
    .filter((f) => fs.statSync(f.path).isFile())

  return Response.json({ files })
}
