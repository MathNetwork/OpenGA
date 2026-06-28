import fs from 'node:fs'
import path from 'node:path'
import { resolveFs } from '@/lib/server/paths'

export const dynamic = 'force-dynamic'
export const runtime = 'nodejs'

/**
 * KaTeX macro table for a project: `.astrolabe/katex-macros.json`
 * (produced by tools/tex2mdx.py). Returns `{}` when absent so callers can
 * always spread it into rehype-katex's `macros` option.
 */
export async function GET(req: Request) {
  const { searchParams } = new URL(req.url)
  const projectPath = searchParams.get('path')
  if (!projectPath) return Response.json({ detail: 'path required' }, { status: 400 })

  const file = path.join(resolveFs(projectPath), '.astrolabe', 'katex-macros.json')
  if (!fs.existsSync(file)) return Response.json({})
  try {
    return Response.json(JSON.parse(fs.readFileSync(file, 'utf8')))
  } catch {
    return Response.json({})
  }
}
