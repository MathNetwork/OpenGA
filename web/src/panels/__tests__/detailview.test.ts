/**
 * DetailView 测试
 *
 * DetailView 是纯布局容器，渲染 EntryDetail。
 */
import { describe, it, expect } from 'vitest'
import * as fs from 'fs'

describe('DetailView — entry 详情', () => {
    const source = fs.readFileSync('src/panels/workspace/DetailView.tsx', 'utf-8')

    it('订阅 selectObjStore', () => {
        expect(source).toContain('selectObjStore')
    })

    it('使用 EntryDetail 组件', () => {
        expect(source).toContain('EntryDetail')
    })

    it('未选中时显示空状态', () => {
        expect(source).toMatch(/Select.*entry|◇/)
    })
})

describe('EntryDetail — entry 展示组件', () => {
    const source = fs.readFileSync('src/panels/workspace/EntryDetail.tsx', 'utf-8')

    it('fetch /api/astrolabe/entries/', () => {
        expect(source).toContain('/api/astrolabe/entries/')
    })

    it('渲染 ref 数组', () => {
        expect(source).toContain('entry.ref')
    })

    it('渲染 record 字段', () => {
        expect(source).toContain('entry.record')
    })

    it('raw JSON fallback 展示（无 plugin 时）', () => {
        expect(source).toContain('JSON.stringify')
    })

    it('点击 ref hash 可以跳转', () => {
        expect(source).toContain('selectObj')
    })
})
