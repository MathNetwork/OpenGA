import fs from 'node:fs'
import path from 'node:path'
import { resolveFs } from '@/lib/server/paths'

export const dynamic = 'force-dynamic'
export const runtime = 'nodejs'

// Absolute-path interface (lean sources live outside the project dir), so
// containment is by file type: only Lean sources are readable here.
const ALLOWED_EXTENSIONS = ['.lean']

export async function GET(req: Request) {
  const { searchParams } = new URL(req.url)
  const raw = searchParams.get('path')
  if (!raw) return Response.json({ detail: 'path required' }, { status: 400 })
  const filePath = path.resolve(resolveFs(raw)) // normalizes any ../ segments
  if (!ALLOWED_EXTENSIONS.includes(path.extname(filePath)))
    return Response.json({ detail: 'Access denied' }, { status: 403 })
  if (!fs.existsSync(filePath) || !fs.statSync(filePath).isFile())
    return Response.json({ detail: `File not found: ${filePath}` }, { status: 404 })

  const line = Number(searchParams.get('line') ?? '1')
  const context = Number(searchParams.get('context') ?? '20')
  const lines = fs.readFileSync(filePath, 'utf8').split('\n')
  const total = lines.length
  const start = Math.max(1, line - context)
  const end = Math.min(total, line + context)
  return Response.json({
    content: lines.slice(start - 1, end).join('\n'),
    startLine: start,
    endLine: end,
    totalLines: total,
  })
}
